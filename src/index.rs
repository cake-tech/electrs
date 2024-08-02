use anyhow::{Context, Result};
use bitcoin::consensus::{deserialize, serialize, Decodable};
use bitcoin::secp256k1::PublicKey;
use bitcoin::{BlockHash, OutPoint, Txid};
use bitcoin_slices::{bsl, Visit, Visitor};
use rayon::prelude::*;
use silentpayments::utils::receiving::{calculate_tweak_data, get_pubkey_from_input};
use std::ops::ControlFlow;
use std::sync::{Arc, Mutex};

use crate::sp::{TweakBlockData, TweakData, VoutData};
use crate::{
    chain::{Chain, NewHeader},
    daemon::Daemon,
    db::{DBStore, Row, WriteBatch},
    metrics::{self, Gauge, Histogram, Metrics},
    signals::ExitFlag,
    types::{
        bsl_txid, HashPrefixRow, HeaderRow, ScriptHash, ScriptHashRow, SerBlock, SpendingPrefixRow,
        TxidRow,
    },
};

#[derive(Clone)]
struct Stats {
    update_duration: Histogram,
    update_size: Histogram,
    height: Gauge,
    db_properties: Gauge,
}

impl Stats {
    fn new(metrics: &Metrics) -> Self {
        Self {
            update_duration: metrics.histogram_vec(
                "index_update_duration",
                "Index update duration (in seconds)",
                "step",
                metrics::default_duration_buckets(),
            ),
            update_size: metrics.histogram_vec(
                "index_update_size",
                "Index update size (in bytes)",
                "step",
                metrics::default_size_buckets(),
            ),
            height: metrics.gauge("index_height", "Indexed block height", "type"),
            db_properties: metrics.gauge("index_db_properties", "Index DB properties", "name"),
        }
    }

    fn observe_duration<T>(&self, label: &str, f: impl FnOnce() -> T) -> T {
        self.update_duration.observe_duration(label, f)
    }

    fn observe_size(&self, label: &str, rows: &[Row]) {
        self.update_size.observe(label, db_rows_size(rows) as f64);
    }

    fn observe_batch(&self, batch: &WriteBatch) {
        self.observe_size("write_funding_rows", &batch.funding_rows);
        self.observe_size("write_spending_rows", &batch.spending_rows);
        self.observe_size("write_txid_rows", &batch.txid_rows);
        self.observe_size("write_header_rows", &batch.header_rows);
        debug!(
            "writing {} funding and {} spending rows from {} transactions, {} blocks",
            batch.funding_rows.len(),
            batch.spending_rows.len(),
            batch.txid_rows.len(),
            batch.header_rows.len()
        );
    }

    fn observe_chain(&self, chain: &Chain) {
        self.height.set("tip", chain.height() as f64);
    }

    fn observe_db(&self, store: &DBStore) {
        for (cf, name, value) in store.get_properties() {
            self.db_properties
                .set(&format!("{}:{}", name, cf), value as f64);
        }
    }
}

/// Confirmed transactions' address index
pub struct Index {
    store: DBStore,
    batch_size: usize,
    lookup_limit: Option<usize>,
    chain: Chain,
    stats: Stats,
    is_ready: bool,
    flush_needed: bool,
    initial_sync_done: bool,
}

impl Index {
    pub(crate) fn load(
        store: DBStore,
        mut chain: Chain,
        metrics: &Metrics,
        batch_size: usize,
        lookup_limit: Option<usize>,
        reindex_last_blocks: usize,
    ) -> Result<Self> {
        if let Some(row) = store.get_tip() {
            match deserialize(&row) {
                Ok(tip) => {
                    let headers = store
                        .read_headers()
                        .into_iter()
                        .map(|row| HeaderRow::from_db_row(&row).header)
                        .collect();
                    chain.load(headers, tip);
                    chain.drop_last_headers(reindex_last_blocks);
                }
                Err(_) => {}
            }
        };
        let stats = Stats::new(metrics);
        stats.observe_chain(&chain);
        stats.observe_db(&store);
        Ok(Index {
            store,
            batch_size,
            lookup_limit,
            chain,
            stats,
            is_ready: false,
            flush_needed: false,
            initial_sync_done: false,
        })
    }

    pub(crate) fn chain(&self) -> &Chain {
        &self.chain
    }

    pub(crate) fn limit_result<T>(&self, entries: impl Iterator<Item = T>) -> Result<Vec<T>> {
        let mut entries = entries.fuse();
        let result: Vec<T> = match self.lookup_limit {
            Some(lookup_limit) => entries.by_ref().take(lookup_limit).collect(),
            None => entries.by_ref().collect(),
        };
        if entries.next().is_some() {
            bail!(">{} index entries, query may take too long", result.len())
        }
        Ok(result)
    }

    pub(crate) fn filter_by_txid(&self, txid: Txid) -> impl Iterator<Item = BlockHash> + '_ {
        self.store
            .iter_txid(TxidRow::scan_prefix(txid))
            .map(|row| HashPrefixRow::from_db_row(&row).height())
            .filter_map(move |height| self.chain.get_block_hash(height))
    }

    pub(crate) fn filter_by_funding(
        &self,
        scripthash: ScriptHash,
    ) -> impl Iterator<Item = BlockHash> + '_ {
        self.store
            .iter_funding(ScriptHashRow::scan_prefix(scripthash))
            .map(|row| HashPrefixRow::from_db_row(&row).height())
            .filter_map(move |height| self.chain.get_block_hash(height))
    }

    pub(crate) fn filter_by_spending(
        &self,
        outpoint: OutPoint,
    ) -> impl Iterator<Item = BlockHash> + '_ {
        self.store
            .iter_spending(SpendingPrefixRow::scan_prefix(outpoint))
            .map(|row| HashPrefixRow::from_db_row(&row).height())
            .filter_map(move |height| self.chain.get_block_hash(height))
    }

    pub(crate) fn silent_payments_sync(
        &mut self,
        daemon: &Daemon,
        exit_flag: &ExitFlag,
        sp_begin_height: Option<usize>,
        sp_min_dust: Option<usize>,
        sp_skip_height: Option<usize>,
    ) -> Result<bool> {
        let mut start = 0;
        // Taproot activates around 709,000 and Silent Payments start appearing > 800,000
        // These numbers are specific to mainnet, for regtest/testnet/signet, sp_begin_height
        // should be specified
        //
        // TODO: make 800_000 a constant whose value network specific
        let initial_height = sp_begin_height.unwrap_or(800_000);

        if let Some(sp_skip_height) = sp_skip_height {
            start = sp_skip_height;
        } else {
            if let Some(row) = self.store.last_sp() {
                let blockhash = deserialize::<BlockHash>(&row).ok().and_then(|blockhash| {
                    let height = self.chain.get_block_height(&blockhash).unwrap_or(0);

                    if height > 0 {
                        Some(height + 1)
                    } else {
                        Some(0)
                    }
                });

                if let Some(blockhash) = blockhash {
                    if blockhash > 0 {
                        start = blockhash;
                    }
                }

                if start == 0 {
                    start = self
                        .store
                        .read_last_tweak()
                        .into_iter()
                        .filter_map(|(key, data)| {
                            let tweak_block_data =
                                TweakBlockData::from_boxed_slice(key.clone(), data.clone());

                            Some(tweak_block_data.block_height as usize)
                        })
                        .collect::<Vec<_>>()[0];
                }
            } else {
                start = initial_height;
            }
        }

        let new_header = self
            .chain
            .get_block_header(start)
            .and_then(|header| Some(NewHeader::from((*header, start))));

        if let Some(new_header) = new_header {
            info!("Looking for sp tweaks in block: {}", start);

            exit_flag
                .poll()
                .with_context(|| format!("indexing interrupted at height: {}", start))?;

            let min_dust = sp_min_dust
                .and_then(|dust| u64::try_from(dust).ok())
                .unwrap_or(546);

            self.sync_blocks(daemon, &[new_header], true, min_dust)?;
        } else {
            if self.flush_needed {
                self.store.flush(); // full compaction is performed on the first flush call
                self.flush_needed = false;
            }
            if !self.is_ready {
                info!("Finished Looking for sp tweaks");
            }
            self.is_ready = true;
            return Ok(true); // no more blocks to index (done for now)
        }

        self.flush_needed = true;
        Ok(false) // sync is not done
    }

    pub(crate) fn get_tweaks(
        &self,
        daemon: &Daemon,
        height: usize,
        historical: bool,
    ) -> serde_json::Value {
        let mut map = serde_json::Map::new();

        let _: Vec<_> = self
            .store
            .read_tweaks(height as u64)
            .into_iter()
            .filter_map(|(key, data)| {
                if !data.is_empty() {
                    let tweak_block_data =
                        TweakBlockData::from_boxed_slice(key.clone(), data.clone());
                    let mut block_response_map = serde_json::Map::new();

                    for tweak_data in tweak_block_data.tx_data {
                        let mut tx_response_map = serde_json::Map::new();
                        let mut send_tweak_data = false;

                        tx_response_map.insert(
                            "tweak".to_string(),
                            serde_json::Value::String(tweak_data.tweak.to_string()),
                        );
                        tx_response_map.insert(
                            "output_pubkeys".to_string(),
                            serde_json::Value::Object(serde_json::Map::new()),
                        );

                        if let Some(vout_map) = tx_response_map.get_mut("output_pubkeys") {
                            if let Some(vout_map) = vout_map.as_object_mut() {
                                for vout in tweak_data.vout_data {
                                    let mut is_unspent = false;

                                    if !historical {
                                        // TODO: probably a faster way to do this, considering
                                        // every client call is going to be doing the same utxo
                                        // lookups over and over again, which is likely putting the
                                        // server under too much load.
                                        //
                                        // since utxos only update every ~10 mins on average, seems
                                        // better to update spent vs unspent directly in the
                                        // database after a new block arrives. One idea would be to
                                        // have three indexes: U, B, and T where U is a taproot
                                        // unspent outputs cache (key: 32 byte key), B is record of
                                        // the last time a specific block of tweaks was read (key:
                                        // block_number), and T is the tweak index (key: block_num,
                                        // value: TweakBlockData). The flow would be:
                                        //
                                        //     1. client makes a request for block X
                                        //     2. check if X in B
                                        //        2a. if yes, continue to step 3
                                        //        2b. if no, filter tweaks by checking the taproot
                                        //            outputs against U (this should be much faster
                                        //            than an rpc call to bitcoind). After
                                        //            filtering, write newly filtered tweaks back
                                        //            to T, and add an entry in B
                                        //     3. send tweak data to client
                                        //     4. every time a new block comes in, wipe B
                                        //
                                        // This way, tweak data is not filtered over and over again
                                        // in the 10 minute period where the UTXO set has not
                                        // changed. When the UTXO set does change, the first time
                                        // the tweak data is read, it is filtered and sent to the
                                        // client and then written back so that the next call
                                        // doesnt need to do the filtering again
                                        //
                                        // Worth mentioning: this means the index has no historical
                                        // data, but ideally it shouldn't: clients who want
                                        // transaction history can do so with a full node or an
                                        // offline tool. This means recovery from backup will give
                                        // you your full wallet balance, but not your full tx
                                        // history
                                        let unspent_response = daemon
                                            .get_tx_out(&tweak_data.txid, vout.vout)
                                            .ok()
                                            .and_then(|result| result);
                                        is_unspent = !unspent_response.is_none();
                                    }

                                    if historical || is_unspent {
                                        send_tweak_data = true;
                                        vout_map.insert(
                                            vout.vout.to_string(),
                                            serde_json::Value::Array(vec![
                                                serde_json::Value::String(
                                                    vout.script_pub_key
                                                        .to_hex_string()
                                                        .replace("5120", ""),
                                                ),
                                                serde_json::Value::Number(vout.amount.into()),
                                            ]),
                                        );
                                    }
                                }
                            }
                        }

                        if send_tweak_data {
                            block_response_map.insert(
                                tweak_data.txid.to_string(),
                                serde_json::Value::Object(tx_response_map),
                            );
                        }
                    }

                    if !block_response_map.is_empty() {
                        map.insert(
                            tweak_block_data.block_height.to_string(),
                            serde_json::Value::Object(block_response_map),
                        );
                    }

                    Some(())
                } else {
                    None
                }
            })
            .collect();

        serde_json::Value::Object(map)
    }

    // Return `Ok(true)` when the chain is fully synced and the index is compacted.
    pub(crate) fn sync(
        &mut self,
        daemon: &Daemon,
        exit_flag: &ExitFlag,
        sp_min_dust: Option<usize>,
    ) -> Result<bool> {
        let new_headers = self
            .stats
            .observe_duration("headers", || daemon.get_new_headers(&self.chain))?;
        match (new_headers.first(), new_headers.last()) {
            (Some(first), Some(last)) => {
                let count = new_headers.len();
                info!(
                    "indexing {} blocks: [{}..{}]",
                    count,
                    first.height(),
                    last.height()
                );
            }
            _ => {
                if !self.initial_sync_done {
                    self.initial_sync_done = true;
                }
                return Ok(true); // no more blocks to index (done for now)
            }
        }
        for chunk in new_headers.chunks(self.batch_size) {
            exit_flag.poll().with_context(|| {
                format!(
                    "indexing interrupted at height: {}",
                    chunk.first().unwrap().height()
                )
            })?;
            let min_dust = sp_min_dust
                .and_then(|dust| u64::try_from(dust).ok())
                .unwrap_or(0);

            self.sync_blocks(daemon, chunk, false, min_dust)?;
        }
        self.chain.update(new_headers);
        self.stats.observe_chain(&self.chain);
        Ok(false) // sync is not done
    }

    fn sync_blocks(
        &mut self,
        daemon: &Daemon,
        chunk: &[NewHeader],
        sp: bool,
        min_dust: u64,
    ) -> Result<()> {
        let blockhashes: Vec<BlockHash> = chunk.iter().map(|h| h.hash()).collect();
        let mut heights = chunk.iter().map(|h| h.height());
        let mut batch = WriteBatch::default();

        if !sp {
            let scan_block = |blockhash, block| {
                if let Some(height) = heights.next() {
                    self.stats.observe_duration("block", || {
                        index_single_block(blockhash, block, height, &mut batch);
                    });
                    self.stats.height.set("tip", height as f64);
                };
            };

            daemon.for_blocks(blockhashes, scan_block)?;
        } else {
            let scan_block_for_sp = |blockhash, block| {
                if let Some(height) = heights.next() {
                    scan_single_block_for_silent_payments(
                        daemon, height, blockhash, block, &mut batch, min_dust,
                    );
                };
            };

            daemon.for_blocks(blockhashes, scan_block_for_sp)?;
        }

        batch.sort();
        self.stats.observe_batch(&batch);
        self.stats
            .observe_duration("write", || self.store.write(&batch));
        self.stats.observe_db(&self.store);
        Ok(())
    }

    pub(crate) fn is_ready(&self) -> bool {
        self.is_ready
    }
}

fn db_rows_size(rows: &[Row]) -> usize {
    rows.iter().map(|key| key.len()).sum()
}

fn index_single_block(
    block_hash: BlockHash,
    block: SerBlock,
    height: usize,
    batch: &mut WriteBatch,
) {
    struct IndexBlockVisitor<'a> {
        batch: &'a mut WriteBatch,
        height: usize,
    }

    impl<'a> Visitor for IndexBlockVisitor<'a> {
        fn visit_transaction(&mut self, tx: &bsl::Transaction) -> ControlFlow<()> {
            let txid = bsl_txid(tx);
            self.batch
                .txid_rows
                .push(TxidRow::row(txid, self.height).to_db_row());

            ControlFlow::Continue(())
        }

        fn visit_tx_out(&mut self, _vout: usize, tx_out: &bsl::TxOut) -> ControlFlow<()> {
            let script = bitcoin::Script::from_bytes(tx_out.script_pubkey());
            // skip indexing unspendable outputs
            if !script.is_provably_unspendable() {
                let row = ScriptHashRow::row(ScriptHash::new(script), self.height);
                self.batch.funding_rows.push(row.to_db_row());
            }
            ControlFlow::Continue(())
        }

        fn visit_tx_in(&mut self, _vin: usize, tx_in: &bsl::TxIn) -> ControlFlow<()> {
            let prevout: OutPoint = tx_in.prevout().into();

            // skip indexing coinbase transactions' input
            if prevout.is_null() {
                return ControlFlow::Continue(());
            }

            let row = SpendingPrefixRow::row(prevout, self.height);
            self.batch.spending_rows.push(row.to_db_row());

            ControlFlow::Continue(())
        }

        fn visit_block_header(&mut self, header: &bsl::BlockHeader) -> ControlFlow<()> {
            match bitcoin::block::Header::consensus_decode(&mut header.as_ref()) {
                Ok(header) => {
                    self.batch
                        .header_rows
                        .push(HeaderRow::new(header).to_db_row());
                }
                Err(_) => {}
            };
            ControlFlow::Continue(())
        }
    }

    let mut index_block = IndexBlockVisitor { batch, height };
    match bsl::Block::visit(&block, &mut index_block) {
        Ok(_) => {}
        Err(_) => {}
    };
    batch.tip_row = serialize(&block_hash).into_boxed_slice();
}

fn scan_single_block_for_silent_payments(
    daemon: &Daemon,
    block_height: usize,
    block_hash: BlockHash,
    block: SerBlock,
    batch: &mut WriteBatch,
    min_dust: u64,
) {
    struct IndexBlockVisitor<'a> {
        daemon: &'a Daemon,
        min_dust: u64,
        tweak_block_data: &'a mut TweakBlockData,
    }

    impl<'a> Visitor for IndexBlockVisitor<'a> {
        fn visit_transaction(&mut self, tx: &bsl::Transaction) -> core::ops::ControlFlow<()> {
            let parsed_tx = match deserialize::<bitcoin::Transaction>(tx.as_ref()) {
                Ok(parsed_tx) => parsed_tx,
                Err(_) => return ControlFlow::Continue(()),
            };

            if parsed_tx.is_coinbase() {
                return ControlFlow::Continue(());
            };

            let txid = bsl_txid(tx);
            let output_pubkeys: Arc<Mutex<Vec<VoutData>>> =
                Arc::new(Mutex::new(Vec::with_capacity(parsed_tx.output.len())));

            parsed_tx
                .output
                .clone()
                .into_par_iter()
                .enumerate()
                .for_each(|(i, o)| {
                    let amount = o.value.to_sat();
                    if o.script_pubkey.is_p2tr() && amount >= self.min_dust {
                        let unspent_response = self
                            .daemon
                            .get_tx_out(&txid, i.try_into().unwrap())
                            .ok()
                            .and_then(|result| result);
                        let is_unspent = !unspent_response.is_none();

                        if is_unspent {
                            output_pubkeys.lock().unwrap().push(VoutData {
                                vout: i.try_into().unwrap(),
                                amount,
                                script_pub_key: o.script_pubkey,
                            });
                        }
                    }
                });

            if output_pubkeys.lock().unwrap().is_empty() {
                return ControlFlow::Continue(());
            }

            let pubkeys = Arc::new(Mutex::new(Vec::with_capacity(parsed_tx.input.len())));
            let outpoints = Arc::new(Mutex::new(Vec::with_capacity(parsed_tx.input.len())));

            parsed_tx.input.clone().into_par_iter().for_each(|i| {
                let prev_txid = i.previous_output.txid;
                let prev_vout = i.previous_output.vout;

                // Collect outpoints from all of the inputs, not just the silent payment eligible
                // inputs. This is relevant for transactions that have a mix of silent payments
                // eligible and non-eligible inputs, where the smallest outpoint is for one of the
                // non-eligible inputs
                outpoints
                    .lock()
                    .unwrap()
                    .push((prev_txid.to_string(), prev_vout));
                let prev_tx = self.daemon.get_transaction(&prev_txid, None).ok();
                let prevout: Option<bitcoin::TxOut> = prev_tx.and_then(|prev_tx| {
                    let index: Option<usize> = prev_vout.try_into().ok();
                    index.and_then(move |index| prev_tx.output.get(index).cloned())
                });

                if let Some(prevout) = prevout {
                    match get_pubkey_from_input(
                        i.script_sig.as_bytes(),
                        &i.witness.to_vec(),
                        prevout.script_pubkey.as_bytes(),
                    ) {
                        Ok(Some(pubkey)) => pubkeys.lock().unwrap().push(pubkey),
                        Ok(None) => (),
                        Err(_) => {}
                    }
                }
            });

            let binding = pubkeys.lock().unwrap();
            let pubkeys_ref: Vec<&PublicKey> = binding.iter().collect();

            if !pubkeys_ref.is_empty() {
                if let Some(tweak) =
                    calculate_tweak_data(&pubkeys_ref, &outpoints.lock().unwrap()).ok()
                {
                    self.tweak_block_data.tx_data.push(TweakData {
                        txid,
                        tweak,
                        vout_data: output_pubkeys.lock().unwrap().to_vec(),
                    });
                }
            }

            ControlFlow::Continue(())
        }
    }

    if let Some(height) = u64::try_from(block_height).ok() {
        let mut tweak_block_data = TweakBlockData::new(height);

        let mut index_block = IndexBlockVisitor {
            daemon,
            tweak_block_data: &mut tweak_block_data,
            min_dust,
        };
        match bsl::Block::visit(&block, &mut index_block) {
            Ok(_) => {}
            Err(_) => {}
        };

        batch.tweak_rows.push(tweak_block_data.into_boxed_slice());
        batch.sp_tip_row = serialize(&block_hash).into_boxed_slice();
    }
}
