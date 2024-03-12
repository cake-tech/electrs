use anyhow::{Context, Result};
use bitcoin::consensus::{deserialize, serialize, Decodable};
use bitcoin::hashes::Hash;
use bitcoin::hex::DisplayHex;
use bitcoin::secp256k1::PublicKey;
use bitcoin::{BlockHash, OutPoint, Txid};
use bitcoin_slices::{bsl, Visit, Visitor};
use silentpayments::utils::receiving::recipient_calculate_tweak_data;
use std::collections::HashMap;
use std::ops::ControlFlow;

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
    ) -> Result<bool> {
        let mut new_headers: Vec<NewHeader> = Vec::with_capacity(200);
        let start: usize;

        if let Some(row) = self.store.last_sp() {
            match deserialize::<BlockHash>(&row) {
                Ok(blockhash) => {
                    start = self
                        .chain
                        .get_block_height(&blockhash)
                        .unwrap_or(2581656 - 1)
                        + 1;
                }
                Err(_) => {
                    start = self
                        .store
                        .read_last_tweak()
                        .into_iter()
                        .filter_map(|(blockhash, _)| {
                            Some(match deserialize::<BlockHash>(&blockhash) {
                                Ok(blockhash) => {
                                    self.chain
                                        .get_block_height(&blockhash)
                                        .unwrap_or(2581656 - 1)
                                        + 1
                                }
                                Err(_) => 2581656,
                            })
                        })
                        .collect::<Vec<_>>()[0];
                }
            };
        } else {
            start = 2581656;
        }
        let end = if start + 200 < self.chain.height() {
            start + 200
        } else {
            self.chain.height()
        };
        for block_height in start..end + 1 {
            match self.chain.get_block_header(block_height) {
                Some(new_header) => {
                    new_headers.push(NewHeader::from((*new_header, block_height)));
                }
                None => {}
            };
        }
        match (new_headers.first(), new_headers.last()) {
            (Some(first), Some(last)) => {
                let count = new_headers.len();
                info!(
                    "Looking for sp tweaks in {} blocks: [{}..{}]",
                    count,
                    first.height(),
                    last.height()
                );
            }
            _ => {
                if self.flush_needed {
                    self.store.flush(); // full compaction is performed on the first flush call
                    self.flush_needed = false;
                }
                self.is_ready = true;
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
            self.sync_blocks(daemon, chunk, true)?;
        }
        self.flush_needed = true;
        Ok(false) // sync is not done
    }

    pub(crate) fn get_tweaks(&self, height: usize, count: usize) -> serde_json::Value {
        let mut map = serde_json::Map::new();

        let _: Vec<_> = self
            .store
            .read_tweaks(height as u64, count as u64)
            .into_iter()
            .filter_map(|(block_height_vec, data)| {
                if !data.is_empty() {
                    let mut chunk = 0;

                    while data.len() > chunk {
                        let mut obj = serde_json::Map::new();

                        let mut txid = [0u8; 32];
                        txid.copy_from_slice(&data[chunk..chunk + 32]);
                        chunk += 32;
                        txid.reverse();

                        let mut tweak = [0u8; 33];
                        tweak.copy_from_slice(&data[chunk..chunk + 33]);
                        chunk += 33;
                        obj.insert(
                            "tweak".to_string(),
                            serde_json::Value::String(tweak.as_hex().to_string()),
                        );

                        let mut output_pubkeys_len = [0u8; 8];
                        output_pubkeys_len.copy_from_slice(&data[chunk..chunk + 8]);
                        chunk += 8;

                        let chunk_size = 46;

                        data[chunk..]
                            .chunks(u64::from_be_bytes(output_pubkeys_len) as usize)
                            .next()?
                            .chunks(chunk_size)
                            .for_each(|pubkey| {
                                let mut pubkey_chunk = 0;

                                let mut vout = [0u8; 4];
                                vout.copy_from_slice(&pubkey[..4]);
                                pubkey_chunk += 4;

                                let mut amount = [0u8; 8];
                                amount.copy_from_slice(&pubkey[pubkey_chunk..pubkey_chunk + 8]);
                                pubkey_chunk += 8;

                                let pubkey_hex = serde_json::Value::String(
                                    pubkey[pubkey_chunk + 2..].as_hex().to_string(),
                                );
                                pubkey_chunk += 34;
                                chunk += pubkey_chunk;

                                if let Some(value) = obj.get_mut("output_pubkeys") {
                                    if let Some(vout_map) = value.as_object_mut() {
                                        vout_map.insert(
                                            u32::from_be_bytes(vout).to_string(),
                                            serde_json::json!({
                                                "pubkey": pubkey_hex,
                                                "amount": u64::from_be_bytes(amount).to_string()
                                            }),
                                        );
                                    };
                                } else {
                                    let mut vout_map = serde_json::Map::new();
                                    vout_map.insert(
                                        u32::from_be_bytes(vout).to_string(),
                                        serde_json::json!({
                                            "pubkey": pubkey_hex,
                                            "amount": u64::from_be_bytes(amount).to_string()
                                        }),
                                    );

                                    obj.insert(
                                        "output_pubkeys".to_string(),
                                        serde_json::Value::Object(vout_map),
                                    );
                                }
                            });

                        let mut height_value = [0u8; 8];
                        height_value.copy_from_slice(&block_height_vec);
                        let height = u64::from_be_bytes(height_value);

                        if let Some(value) = map.get_mut(&height.to_string()) {
                            if let Some(value_map) = value.as_object_mut() {
                                value_map.insert(
                                    Txid::from_byte_array(txid).to_string(),
                                    serde_json::Value::Object(obj),
                                );
                            }
                        } else {
                            let mut new_map = serde_json::Map::new();
                            new_map.insert(
                                Txid::from_byte_array(txid).to_string(),
                                serde_json::Value::Object(obj),
                            );
                            map.insert(height.to_string(), serde_json::Value::Object(new_map));
                        }
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
    pub(crate) fn sync(&mut self, daemon: &Daemon, exit_flag: &ExitFlag) -> Result<bool> {
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
            self.sync_blocks(daemon, chunk, false)?;
        }
        self.chain.update(new_headers);
        self.stats.observe_chain(&self.chain);
        self.flush_needed = true;
        Ok(false) // sync is not done
    }

    fn sync_blocks(&mut self, daemon: &Daemon, chunk: &[NewHeader], sp: bool) -> Result<()> {
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
                    self.stats.observe_duration("block_sp", || {
                        scan_single_block_for_silent_payments(
                            self, daemon, blockhash, block, &mut batch,
                        );
                    });
                    self.stats.height.set("sp", height as f64);
                };
            };

            daemon.for_blocks(blockhashes, scan_block_for_sp)?;
        }

        let heights: Vec<_> = heights.collect();
        assert!(
            heights.is_empty(),
            "some blocks were not indexed: {:?}",
            heights
        );
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
            if !prevout.is_null() {
                let row = SpendingPrefixRow::row(prevout, self.height);
                self.batch.spending_rows.push(row.to_db_row());
            }
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
    index: &Index,
    daemon: &Daemon,
    block_hash: BlockHash,
    block: SerBlock,
    batch: &mut WriteBatch,
) {
    struct IndexBlockVisitor<'a> {
        daemon: &'a Daemon,
        index: &'a Index,
        map: &'a mut HashMap<BlockHash, HashMap<Txid, HashMap<String, Vec<u8>>>>,
        batch: &'a mut WriteBatch,
    }

    impl<'a> Visitor for IndexBlockVisitor<'a> {
        fn visit_transaction(&mut self, tx: &bsl::Transaction) -> core::ops::ControlFlow<()> {
            match deserialize::<bitcoin::Transaction>(tx.as_ref()) {
                Ok(parsed_tx) => {
                    if parsed_tx.is_coinbase() {
                        return ControlFlow::Continue(());
                    };

                    let txid = bsl_txid(tx);

                    let mut output_pubkeys: Vec<u8> = Vec::with_capacity(parsed_tx.output.len());

                    for (i, o) in parsed_tx.output.iter().enumerate() {
                        if o.script_pubkey.is_p2tr() {
                            let outpoint = OutPoint {
                                txid,
                                vout: i.try_into().expect("Unexpectedly high vout"),
                            };
                            if self
                                .index
                                .store
                                .iter_spending(SpendingPrefixRow::scan_prefix(outpoint))
                                .next()
                                .is_none()
                            {
                                output_pubkeys.extend(outpoint.vout.to_be_bytes());
                                output_pubkeys.extend(o.value.to_sat().to_be_bytes());
                                output_pubkeys.extend(o.script_pubkey.to_bytes());
                            }
                        }
                    }

                    if output_pubkeys.is_empty() {
                        return ControlFlow::Continue(());
                    }

                    // Iterate over inputs
                    let mut pubkeys: Vec<PublicKey> = Vec::with_capacity(parsed_tx.input.len());
                    let mut outpoints: Vec<(String, u32)> =
                        Vec::with_capacity(parsed_tx.input.len());
                    for i in parsed_tx.input.iter() {
                        // get the prevout script pubkey
                        let prev_txid = i.previous_output.txid;
                        outpoints.push((prev_txid.to_string(), i.previous_output.vout));
                        match self.daemon.get_transaction(&prev_txid, None) {
                            Ok(prev_tx) => {
                                let index: usize = i
                                    .previous_output
                                    .vout
                                    .try_into()
                                    .expect("Unexpectedly high vout");

                                if let Some(prevout) = prev_tx.output.get(index) {
                                    // if prevout.script_pubkey.is_p2tr() {
                                    //     if let Some(block_hash) =
                                    //         self.index.filter_by_txid(prev_txid).next()
                                    //     {
                                    //         if let Some(height) =
                                    //             self.index.chain.get_block_height(&block_hash)
                                    //         {
                                    //             match serde_json::from_value::<
                                    //                 HashMap<String, serde_json::Value>,
                                    //             >(
                                    //                 self.index.get_tweaks(height, 1)
                                    //             ) {
                                    //                 Ok(mut existing_script_pubkeys_by_tweak) => {
                                    //                     match existing_script_pubkeys_by_tweak
                                    //                         .get_mut(&prev_txid.to_string())
                                    //                     {
                                    //                         Some(tx) => {
                                    //                             let mut vout_pubkey_array: Vec<u8> =
                                    //                                 Vec::new();
                                    //                             match serde_json::from_value::<
                                    //                                 HashMap<String, String>,
                                    //                             >(
                                    //                                 tx["output_pubkeys"].to_owned(),
                                    //                             ) {
                                    //                                 Ok(pubkeys_obj) => {
                                    //                                     let mut should_add = false;
                                    //
                                    //                                     let _: Vec<_> = pubkeys_obj
                                    //                                         .into_iter()
                                    //                                         .map(
                                    //                                             |(vout, pubkey)| {
                                    //                                                 if vout
                                    //                                     == i.previous_output
                                    //                                         .vout
                                    //                                         .to_string()
                                    //                                     && pubkey
                                    //                                         == prevout
                                    //                                             .script_pubkey
                                    //                                             .to_hex_string()
                                    //                                 {
                                    //                                     println!(
                                    //                     "found a matching spend {:?}, {:?}, {:?}",
                                    //                     vout, pubkey, txid
                                    //                 );
                                    //
                                    //                                     should_add = true;
                                    //                                 } else {
                                    //                                     let outpoint = OutPoint {
                                    //                                         txid,
                                    //                                         vout: i
                                    //                                             .previous_output
                                    //                                             .vout,
                                    //                                     };
                                    //                                     let mut vout_array =
                                    //                                         [0u8; 4];
                                    //                                     vout_array.copy_from_slice(
                                    //                                         &outpoint
                                    //                                             .vout
                                    //                                             .to_be_bytes(),
                                    //                                     );
                                    //                                     vout_pubkey_array
                                    //                                         .extend(vout_array);
                                    //
                                    //                                     vout_pubkey_array.extend(
                                    //                                         pubkey.as_bytes(),
                                    //                                     );
                                    //
                                    //                                     should_add = false;
                                    //                                 }
                                    //                                             },
                                    //                                         )
                                    //                                         .collect();
                                    //
                                    //                                     if should_add {
                                    //                                         let mut value: Vec<u8> =
                                    //                                             height
                                    //                                                 .to_be_bytes()
                                    //                                                 .to_vec();
                                    //
                                    //                                         value.extend(
                                    //                                             prev_txid
                                    //                                                 .to_byte_array(
                                    //                                                 ),
                                    //                                         );
                                    //
                                    //                                         match
                                    //                                     serde_json::from_value::<String>(
                                    //                                         tx["tweak"].to_owned(),
                                    //                                     )
                                    //                                                         {
                                    //                                                             Ok(tweak) => {
                                    //                                         value.extend(
                                    //                                             tweak.as_bytes(),
                                    //                                         );
                                    //
                                    //                                         value.extend(
                                    //                                             vout_pubkey_array
                                    //                                                 .len()
                                    //                                                 .to_be_bytes(),
                                    //                                         );
                                    //                                         value.extend(
                                    //                                             vout_pubkey_array,
                                    //                                         );
                                    //                                         self.batch.tweak_rows.push(
                                    //                                     value.into_boxed_slice(),
                                    //                                 );
                                    //                                                             },
                                    //                                                                 Err(_)=> {}
                                    //
                                    //
                                    //                                                         };
                                    //                                     }
                                    //                                 }
                                    //                                 Err(_) => {}
                                    //                             };
                                    //                         }
                                    //                         None => {}
                                    //                     };
                                    //                 }
                                    //                 Err(_) => {}
                                    //             }
                                    //         };
                                    //     }
                                    // }

                                    match crate::sp::get_pubkey_from_input(&crate::sp::VinData {
                                        script_sig: i.script_sig.to_bytes(),
                                        txinwitness: i.witness.to_vec(),
                                        script_pub_key: prevout.script_pubkey.to_bytes(),
                                    }) {
                                        Ok(Some(pubkey)) => pubkeys.push(pubkey),
                                        Ok(None) => (),
                                        Err(_) => (),
                                    }
                                };
                            }
                            Err(_) => {}
                        };
                    }

                    let pubkeys_ref: Vec<&PublicKey> = pubkeys.iter().collect();

                    if !pubkeys_ref.is_empty() {
                        match recipient_calculate_tweak_data(&pubkeys_ref, &outpoints) {
                            Ok(tweak) => {
                                // check in which block is this transaction
                                if let Some(block_hash) = self.index.filter_by_txid(txid).next() {
                                    let mut obj: HashMap<String, Vec<u8>> = HashMap::new();
                                    obj.insert(
                                        "tweak".to_string(),
                                        Vec::from_iter(tweak.serialize()),
                                    );
                                    obj.insert(
                                        "output_pubkeys".to_string(),
                                        output_pubkeys.into_iter().collect(),
                                    );

                                    if let Some(value) = self.map.get_mut(&block_hash) {
                                        value.insert(txid, obj);
                                    } else {
                                        self.map
                                            .insert(block_hash, HashMap::from_iter([(txid, obj)]));
                                    }
                                }
                            }
                            Err(_) => {}
                        };
                    }

                    ControlFlow::Continue(())
                }
                // TODO: not scanned and skipped?
                Err(_) => ControlFlow::Continue(()),
            }
        }
    }

    let mut map: HashMap<BlockHash, HashMap<Txid, HashMap<String, Vec<u8>>>> =
        HashMap::with_capacity(index.batch_size);
    let mut index_block = IndexBlockVisitor {
        daemon,
        index,
        map: &mut map,
        batch,
    };
    match bsl::Block::visit(&block, &mut index_block) {
        Ok(_) => {}
        Err(_) => {}
    };
    for (hash, tweaks_by_txid) in map {
        if let Some(height) = index.chain.get_block_height(&hash) {
            match u64::try_from(height) {
                Ok(value) => {
                    let mut value = value.to_be_bytes().to_vec();

                    for (txid, tweak_pubkey_obj) in tweaks_by_txid {
                        let mut txid_value = [0u8; 32];
                        txid_value.copy_from_slice(&txid[..]);
                        txid_value.reverse();

                        value.extend(txid_value);
                        value.extend(&tweak_pubkey_obj["tweak"]);
                        value.extend(&tweak_pubkey_obj["output_pubkeys"].len().to_be_bytes());
                        value.extend(&tweak_pubkey_obj["output_pubkeys"]);
                    }

                    batch.tweak_rows.push(value.into_boxed_slice());
                }
                Err(_) => {}
            };
        }
    }
    batch.sp_tip_row = serialize(&block_hash).into_boxed_slice();
}
