use bitcoin::Amount;
use bitcoin::Witness;
#[cfg(feature = "liquid")]
use elements::confidential;
use hex::DisplayHex;
use rayon::prelude::*;

#[cfg(not(feature = "liquid"))]
use bitcoin::consensus::encode::{deserialize, serialize};
#[cfg(feature = "liquid")]
use elements::encode::{deserialize, serialize};

use silentpayments::utils::receiving::{calculate_tweak_data, get_pubkey_from_input};

use std::convert::TryInto;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use crate::config::Config;
use crate::daemon::Daemon;
use crate::errors::*;
use crate::metrics::{Gauge, HistogramOpts, HistogramTimer, HistogramVec, MetricOpts, Metrics};
use crate::util::{
    full_hash, has_prevout, is_spendable, BlockId, BlockMeta, HeaderEntry, ScriptToAddr,
};
use crate::{
    chain::{BlockHash, Network, OutPoint, Transaction, Txid},
    daemon::tx_from_value,
};

use crate::new_index::db::{DBFlush, DBRow, DB};
use crate::new_index::fetch::{start_fetcher, BlockEntry, FetchFrom};

#[cfg(feature = "liquid")]
use crate::elements::asset;

use crate::new_index::{
    schema::{
        get_previous_txos, lookup_txos, BlockRow, FundingInfo, SpendingInfo, SpendingInput,
        TweakData, TweakTxRow, TxConfRow, TxEdgeRow, TxHistoryInfo, TxHistoryRow, TxOutRow, TxRow,
        VoutData,
    },
    Store,
};

pub const MIN_SP_TWEAK_HEIGHT: usize = 823_807; // 01/01/2024

pub struct Indexer {
    store: Arc<Store>,
    flush: DBFlush,
    from: FetchFrom,
    iconfig: IndexerConfig,
    duration: HistogramVec,
    tip_metric: Gauge,
}

struct IndexerConfig {
    light_mode: bool,
    address_search: bool,
    index_unspendables: bool,
    network: Network,
    #[cfg(feature = "liquid")]
    parent_network: crate::chain::BNetwork,
    sp_begin_height: Option<usize>,
    sp_min_dust: Option<usize>,
    sp_check_spends: bool,
    skip_history: bool,
    skip_tweaks: bool,
}

impl From<&Config> for IndexerConfig {
    fn from(config: &Config) -> Self {
        IndexerConfig {
            light_mode: config.light_mode,
            address_search: config.address_search,
            index_unspendables: config.index_unspendables,
            network: config.network_type,
            #[cfg(feature = "liquid")]
            parent_network: config.parent_network,
            sp_begin_height: config.sp_begin_height,
            sp_min_dust: config.sp_min_dust,
            sp_check_spends: config.sp_check_spends,
            skip_history: config.skip_history,
            skip_tweaks: config.skip_tweaks,
        }
    }
}

impl Indexer {
    pub fn open(store: Arc<Store>, from: FetchFrom, config: &Config, metrics: &Metrics) -> Self {
        Indexer {
            store,
            flush: DBFlush::Disable,
            from,
            iconfig: IndexerConfig::from(config),
            duration: metrics.histogram_vec(
                HistogramOpts::new("index_duration", "Index update duration (in seconds)"),
                &["step"],
            ),
            tip_metric: metrics.gauge(MetricOpts::new("tip_height", "Current chain tip height")),
        }
    }

    fn start_timer(&self, name: &str) -> HistogramTimer {
        self.duration.with_label_values(&[name]).start_timer()
    }

    fn headers_to_add(&self, new_headers: &[HeaderEntry]) -> Vec<HeaderEntry> {
        let added_blockhashes = self.store.added_blockhashes.read().unwrap();
        new_headers
            .iter()
            .filter(|e| !added_blockhashes.contains(e.hash()))
            .cloned()
            .collect()
    }

    fn headers_to_index(&mut self, new_headers: &[HeaderEntry]) -> Vec<HeaderEntry> {
        let indexed_blockhashes = self.store.indexed_blockhashes();
        self.get_headers_to_use(indexed_blockhashes.len(), new_headers, 0)
            .iter()
            .filter(|e| !indexed_blockhashes.contains(e.hash()))
            .cloned()
            .collect()
    }

    fn headers_to_tweak(&mut self, new_headers: &[HeaderEntry]) -> Vec<HeaderEntry> {
        let tweaked_blockhashes = self.store.tweaked_blockhashes();
        let start_height = self.iconfig.sp_begin_height.unwrap_or(MIN_SP_TWEAK_HEIGHT);

        self.get_headers_to_use(tweaked_blockhashes.len(), new_headers, start_height)
            .iter()
            .filter(|e| !tweaked_blockhashes.contains(e.hash()) && e.height() >= start_height)
            .cloned()
            .collect()
    }

    fn start_auto_compactions(&self, db: &DB) {
        let key = b"F".to_vec();
        if db.get(&key).is_none() {
            db.full_compaction();
            db.put_sync(&key, b"");
            assert!(db.get(&key).is_some());
        }
        db.enable_auto_compaction();
    }

    fn get_not_indexed_headers(
        &self,
        daemon: &Daemon,
        tip: &BlockHash,
    ) -> Result<Vec<HeaderEntry>> {
        let indexed_headers = self.store.indexed_headers.read().unwrap();
        let new_headers = daemon.get_new_headers(&indexed_headers, &tip)?;
        let result = indexed_headers.order(new_headers);

        if let Some(tip) = result.last() {
            info!("{:?} ({} left to index)", tip, result.len());
        };
        Ok(result)
    }

    fn get_all_indexed_headers(&self) -> Result<Vec<HeaderEntry>> {
        let headers = self.store.indexed_headers.read().unwrap();
        let all_headers = headers.iter().cloned().collect::<Vec<_>>();

        Ok(all_headers)
    }

    fn get_headers_to_use(
        &mut self,
        lookup_len: usize,
        new_headers: &[HeaderEntry],
        start_height: usize,
    ) -> Vec<HeaderEntry> {
        let all_indexed_headers = self.get_all_indexed_headers().unwrap();
        let count_total_indexed = all_indexed_headers.len() - start_height;

        // Should have indexed more than what already has been indexed, use all headers
        if count_total_indexed > lookup_len {
            let count_left_to_index = lookup_len - count_total_indexed;

            if let FetchFrom::BlkFiles = self.from {
                if count_left_to_index < all_indexed_headers.len() / 2 {
                    self.from = FetchFrom::BlkFilesReverse;
                }
            }

            return all_indexed_headers;
        } else {
            // Just needs to index new headers
            return new_headers.to_vec();
        }
    }

    pub fn update(&mut self, daemon: &Daemon) -> Result<BlockHash> {
        let daemon = daemon.reconnect()?;
        let tip = daemon.getbestblockhash()?;
        let headers_not_indexed = self.get_not_indexed_headers(&daemon, &tip)?;

        let to_add = self.headers_to_add(&headers_not_indexed);
        if !to_add.is_empty() {
            debug!(
                "adding transactions from {} blocks using {:?}",
                to_add.len(),
                self.from
            );
            start_fetcher(self.from, &daemon, to_add)?.map(|blocks| self.add(&blocks));
            self.start_auto_compactions(&self.store.txstore_db());
        }

        if !self.iconfig.skip_history {
            let to_index = self.headers_to_index(&headers_not_indexed);
            if !to_index.is_empty() {
                debug!(
                    "indexing history from {} blocks using {:?}",
                    to_index.len(),
                    self.from
                );
                start_fetcher(self.from, &daemon, to_index)?.map(|blocks| self.index(&blocks));
                self.start_auto_compactions(&self.store.history_db());
            }
        } else {
            debug!("Skipping history indexing");
        }

        if !self.iconfig.skip_tweaks {
            let to_tweak = self.headers_to_tweak(&headers_not_indexed);
            let total = to_tweak.len();
            if !to_tweak.is_empty() {
                debug!(
                    "indexing sp tweaks from {} blocks using {:?}",
                    to_tweak.len(),
                    self.from
                );
                start_fetcher(self.from, &daemon, to_tweak)?
                    .map(|blocks| self.tweak(&blocks, &daemon, total));
                self.start_auto_compactions(&self.store.tweak_db());
            }
        } else {
            debug!("Skipping tweaks indexing");
        }

        if let DBFlush::Disable = self.flush {
            debug!("flushing to disk");
            self.store.txstore_db().flush();
            self.store.history_db().flush();
            self.flush = DBFlush::Enable;
        }

        // update the synced tip *after* the new data is flushed to disk
        debug!("updating synced tip to {:?}", tip);
        self.store.txstore_db().put_sync(b"t", &serialize(&tip));

        let mut headers = self.store.indexed_headers.write().unwrap();
        headers.apply(headers_not_indexed);
        assert_eq!(tip, *headers.tip());

        if let FetchFrom::BlkFiles = self.from {
            self.from = FetchFrom::Bitcoind;
        }

        self.tip_metric.set(headers.len() as i64 - 1);

        debug!("finished Indexer update");

        Ok(tip)
    }

    fn add(&self, blocks: &[BlockEntry]) {
        // TODO: skip orphaned blocks?
        let rows = {
            let _timer = self.start_timer("add_process");
            add_blocks(blocks, &self.iconfig)
        };
        {
            let _timer = self.start_timer("add_write");
            self.store.txstore_db().write(rows, self.flush);
        }

        self.store
            .added_blockhashes
            .write()
            .unwrap()
            .extend(blocks.iter().map(|b| b.entry.hash()));
    }

    fn index(&self, blocks: &[BlockEntry]) {
        let previous_txos_map = {
            let _timer = self.start_timer("index_lookup");
            lookup_txos(&self.store.txstore_db(), get_previous_txos(blocks)).unwrap()
        };
        let rows = {
            let _timer = self.start_timer("index_process");
            let added_blockhashes = self.store.added_blockhashes.read().unwrap();
            for b in blocks {
                let blockhash = b.entry.hash();
                // TODO: replace by lookup into txstore_db?
                if !added_blockhashes.contains(blockhash) {
                    panic!("cannot index block {} (missing from store)", blockhash);
                }
            }

            blocks
                .par_iter() // serialization is CPU-intensive
                .map(|b| {
                    let mut rows = vec![];
                    for tx in &b.block.txdata {
                        let height = b.entry.height() as u32;

                        // TODO: return an iterator?

                        // persist history index:
                        //      H{funding-scripthash}{funding-height}F{funding-txid:vout} → ""
                        //      H{funding-scripthash}{spending-height}S{spending-txid:vin}{funding-txid:vout} → ""
                        // persist "edges" for fast is-this-TXO-spent check
                        //      S{funding-txid:vout}{spending-txid:vin} → ""
                        let txid = full_hash(&tx.txid()[..]);
                        for (txo_index, txo) in tx.output.iter().enumerate() {
                            if is_spendable(txo) || self.iconfig.index_unspendables {
                                let history = TxHistoryRow::new(
                                    &txo.script_pubkey,
                                    height,
                                    TxHistoryInfo::Funding(FundingInfo {
                                        txid,
                                        vout: txo_index as u16,
                                        value: txo.value.amount_value(),
                                    }),
                                );
                                rows.push(history.into_row());

                                // for prefix address search, only saved when --address-search is enabled
                                //      a{funding-address-str} → ""
                                if self.iconfig.address_search {
                                    if let Some(row) = txo
                                        .script_pubkey
                                        .to_address_str(self.iconfig.network)
                                        .map(|address| DBRow {
                                            key: [b"a", address.as_bytes()].concat(),
                                            value: vec![],
                                        })
                                    {
                                        rows.push(row);
                                    }
                                }
                            }
                        }
                        for (txi_index, txi) in tx.input.iter().enumerate() {
                            if !has_prevout(txi) {
                                continue;
                            }
                            let prev_txo = previous_txos_map
                                .get(&txi.previous_output)
                                .unwrap_or_else(|| {
                                    panic!("missing previous txo {}", txi.previous_output)
                                });

                            let history = TxHistoryRow::new(
                                &prev_txo.script_pubkey,
                                height,
                                TxHistoryInfo::Spending(SpendingInfo {
                                    txid,
                                    vin: txi_index as u16,
                                    prev_txid: full_hash(&txi.previous_output.txid[..]),
                                    prev_vout: txi.previous_output.vout as u16,
                                    value: prev_txo.value.amount_value(),
                                }),
                            );
                            rows.push(history.into_row());

                            let edge = TxEdgeRow::new(
                                full_hash(&txi.previous_output.txid[..]),
                                txi.previous_output.vout as u16,
                                txid,
                                txi_index as u16,
                            );
                            rows.push(edge.into_row());
                        }

                        // Index issued assets & native asset pegins/pegouts/burns
                        #[cfg(feature = "liquid")]
                        asset::index_confirmed_tx_assets(
                            tx,
                            height,
                            self.iconfig.network,
                            self.iconfig.parent_network,
                            &mut rows,
                        );
                    }
                    rows.push(BlockRow::new_done(full_hash(&b.entry.hash()[..])).into_row()); // mark block as "indexed"
                    rows
                })
                .flatten()
                .collect()
        };
        self.store.history_db().write(rows, self.flush);
    }

    fn tweak(&self, blocks: &[BlockEntry], daemon: &Daemon, total: usize) {
        let _timer = self.start_timer("tweak_process");
        let tweaked_blocks = Arc::new(AtomicUsize::new(0));
        let _: Vec<_> = blocks
            .par_iter() // serialization is CPU-intensive
            .map(|b| {
                let mut rows = vec![];
                let mut tweaks: Vec<Vec<u8>> = vec![];
                let blockhash = full_hash(&b.entry.hash()[..]);
                let blockheight = b.entry.height();

                for tx in &b.block.txdata {
                    self.tweak_transaction(
                        blockheight.try_into().unwrap(),
                        tx,
                        &mut rows,
                        &mut tweaks,
                        daemon,
                    );
                }

                // persist block tweaks index:
                //      W{blockhash} → {tweak1}...{tweakN}
                rows.push(BlockRow::new_tweaks(blockhash, &tweaks).into_row());
                rows.push(BlockRow::new_done(blockhash).into_row());

                self.store.tweak_db().write(rows, self.flush);
                self.store.tweak_db().flush();

                tweaked_blocks.fetch_add(1, Ordering::SeqCst);
                info!(
                    "Sp tweaked block {} of {} total (height: {})",
                    tweaked_blocks.load(Ordering::SeqCst),
                    total,
                    b.entry.height()
                );

                Some(())
            })
            .flatten()
            .collect();
    }

    fn tweak_transaction(
        &self,
        blockheight: u32,
        tx: &Transaction,
        rows: &mut Vec<DBRow>,
        tweaks: &mut Vec<Vec<u8>>,
        daemon: &Daemon,
    ) {
        let txid = &tx.txid();
        let mut output_pubkeys: Vec<VoutData> = Vec::with_capacity(tx.output.len());

        for (txo_index, txo) in tx.output.iter().enumerate() {
            if is_spendable(txo) {
                let amount = (txo.value as Amount).to_sat();
                #[allow(deprecated)]
                if txo.script_pubkey.is_v1_p2tr()
                    && amount >= self.iconfig.sp_min_dust.unwrap_or(1_000) as u64
                {
                    output_pubkeys.push(VoutData {
                        vout: txo_index,
                        amount,
                        script_pubkey: txo.script_pubkey.clone(),
                        spending_input: if self.iconfig.sp_check_spends {
                            self.lookup_spend(&OutPoint {
                                txid: txid.clone(),
                                vout: txo_index as u32,
                            })
                        } else {
                            None
                        },
                    });
                }
            }
        }

        if output_pubkeys.is_empty() {
            return;
        }

        let mut pubkeys = Vec::with_capacity(tx.input.len());
        let mut outpoints = Vec::with_capacity(tx.input.len());

        for txin in tx.input.iter() {
            let prev_txid = txin.previous_output.txid;
            let prev_vout = txin.previous_output.vout;

            // Collect outpoints from all of the inputs, not just the silent payment eligible
            // inputs. This is relevant for transactions that have a mix of silent payments
            // eligible and non-eligible inputs, where the smallest outpoint is for one of the
            // non-eligible inputs
            outpoints.push((prev_txid.to_string(), prev_vout));

            let prev_tx_result = daemon.gettransaction_raw(&prev_txid, None, true);
            if let Ok(prev_tx_value) = prev_tx_result {
                if let Some(prev_tx) = tx_from_value(prev_tx_value.get("hex").unwrap().clone()).ok()
                {
                    if let Some(prevout) = prev_tx.output.get(prev_vout as usize) {
                        match get_pubkey_from_input(
                            &txin.script_sig.to_bytes(),
                            &(txin.witness.clone() as Witness).to_vec(),
                            &prevout.script_pubkey.to_bytes(),
                        ) {
                            Ok(Some(pubkey)) => pubkeys.push(pubkey),
                            Ok(None) => (),
                            Err(_e) => {}
                        }
                    }
                }
            }
        }

        let pubkeys_ref: Vec<_> = pubkeys.iter().collect();
        if !pubkeys_ref.is_empty() {
            if let Some(tweak) = calculate_tweak_data(&pubkeys_ref, &outpoints).ok() {
                // persist tweak index:
                //      K{blockhash}{txid} → {tweak}{serialized-vout-data}
                rows.push(
                    TweakTxRow::new(
                        blockheight,
                        txid.clone(),
                        &TweakData {
                            tweak: tweak.serialize().to_lower_hex_string(),
                            vout_data: output_pubkeys.clone(),
                        },
                    )
                    .into_row(),
                );
                tweaks.push(tweak.serialize().to_vec());
            }
        }
    }

    pub fn fetch_from(&mut self, from: FetchFrom) {
        self.from = from;
    }

    pub fn tx_confirming_block(&self, txid: &Txid) -> Option<BlockId> {
        let _timer = self.start_timer("tx_confirming_block");
        let headers = self.store.indexed_headers.read().unwrap();
        self.store
            .txstore_db()
            .iter_scan(&TxConfRow::filter(&txid[..]))
            .map(TxConfRow::from_row)
            // header_by_blockhash only returns blocks that are part of the best chain,
            // or None for orphaned blocks.
            .find_map(|conf| {
                headers.header_by_blockhash(&deserialize(&conf.key.blockhash).unwrap())
            })
            .map(BlockId::from)
    }

    pub fn lookup_spend(&self, outpoint: &OutPoint) -> Option<SpendingInput> {
        let _timer = self.start_timer("lookup_spend");
        self.store
            .history_db()
            .iter_scan(&TxEdgeRow::filter(&outpoint))
            .map(TxEdgeRow::from_row)
            .find_map(|edge| {
                let txid: Txid = deserialize(&edge.key.spending_txid).unwrap();
                self.tx_confirming_block(&txid).map(|b| SpendingInput {
                    txid,
                    vin: edge.key.spending_vin as u32,
                    confirmed: Some(b),
                })
            })
    }
}

fn add_blocks(block_entries: &[BlockEntry], iconfig: &IndexerConfig) -> Vec<DBRow> {
    // persist individual transactions:
    //      T{txid} → {rawtx}
    //      C{txid}{blockhash}{height} →
    //      O{txid}{index} → {txout}
    // persist block headers', block txids' and metadata rows:
    //      B{blockhash} → {header}
    //      X{blockhash} → {txid1}...{txidN}
    //      M{blockhash} → {tx_count}{size}{weight}
    block_entries
        .par_iter() // serialization is CPU-intensive
        .map(|b| {
            let mut rows = vec![];
            let blockhash = full_hash(&b.entry.hash()[..]);
            let txids: Vec<Txid> = b.block.txdata.iter().map(|tx| tx.txid()).collect();

            for tx in &b.block.txdata {
                rows.push(TxConfRow::new(tx, blockhash).into_row());

                if !iconfig.light_mode {
                    rows.push(TxRow::new(tx).into_row());
                }

                let txid = full_hash(&tx.txid()[..]);
                for (txo_index, txo) in tx.output.iter().enumerate() {
                    if is_spendable(txo) {
                        rows.push(TxOutRow::new(&txid, txo_index, txo).into_row());
                    }
                }
            }

            if !iconfig.light_mode {
                rows.push(BlockRow::new_txids(blockhash, &txids).into_row());
                rows.push(BlockRow::new_meta(blockhash, &BlockMeta::from(b)).into_row());
            }

            rows.push(BlockRow::new_header(&b).into_row());
            rows.push(BlockRow::new_done(blockhash).into_row()); // mark block as "added"
            rows
        })
        .flatten()
        .collect()
}

// Get the amount value as gets stored in the DB and mempool tracker.
// For bitcoin it is the Amount's inner u64, for elements it is the confidential::Value itself.
pub trait GetAmountVal {
    #[cfg(not(feature = "liquid"))]
    fn amount_value(self) -> u64;
    #[cfg(feature = "liquid")]
    fn amount_value(self) -> confidential::Value;
}

#[cfg(not(feature = "liquid"))]
impl GetAmountVal for bitcoin::Amount {
    fn amount_value(self) -> u64 {
        self.to_sat()
    }
}
#[cfg(feature = "liquid")]
impl GetAmountVal for confidential::Value {
    fn amount_value(self) -> confidential::Value {
        self
    }
}
