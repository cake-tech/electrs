use bitcoin::{
    secp256k1::PublicKey,
    ScriptBuf, Txid,
};
use bitcoin_slices::bitcoin_hashes::Hash;

#[derive(Clone, Debug)]
pub struct VoutData {
    pub vout: u32,
    pub amount: u64,
    pub script_pub_key: ScriptBuf,
}

#[derive(Clone, Debug)]
pub struct TweakData {
    pub txid: Txid,
    pub tweak: PublicKey,
    pub vout_data: Vec<VoutData>,
}

impl TweakData {
    pub fn from_boxed_slice(data: Box<[u8]>, passed_chunk: &mut usize) -> Option<Self> {
        let data = data.into_vec();

        let mut chunk = passed_chunk.clone();

        let txid_bytes = &data[chunk..chunk + 32];
        let mut txid = [0u8; 32];
        txid.copy_from_slice(&txid_bytes);
        let txid = Txid::from_slice(&txid).ok();

        chunk += 32;

        let tweak_bytes = &data[chunk..chunk + 33];
        let mut tweak = [0u8; 33];
        tweak.copy_from_slice(&tweak_bytes);
        let tweak = PublicKey::from_slice(&tweak).ok();

        chunk += 33;

        let vout_data_len_bytes = &data[chunk..chunk + 8];
        let mut vout_data_len = [0u8; 8];
        vout_data_len.copy_from_slice(&vout_data_len_bytes);
        let vout_data_len = u64::from_be_bytes(vout_data_len) as usize;

        chunk += 8;

        let mut vout_data = vec![];

        for _ in 0..vout_data_len {
            let vout_bytes = &data[chunk..chunk + 4];
            let mut vout = [0u8; 4];
            vout.copy_from_slice(&vout_bytes);
            let vout = u32::from_be_bytes(vout);

            chunk += 4;

            let amount_bytes = &data[chunk..chunk + 8];
            let mut amount = [0u8; 8];
            amount.copy_from_slice(&amount_bytes);
            let amount = u64::from_be_bytes(amount);

            chunk += 8;

            let script_pub_key_bytes = &data[chunk..chunk + 34];
            let mut script_pub_key = [0u8; 34];
            script_pub_key.copy_from_slice(&script_pub_key_bytes);
            let script_pub_key = ScriptBuf::from_bytes(script_pub_key.to_vec());

            chunk += 34;

            vout_data.push(VoutData {
                vout,
                amount,
                script_pub_key,
            });
        }

        *passed_chunk = chunk;

        if let Some(txid) = txid {
            if let Some(tweak) = tweak {
                return Some(Self {
                    txid,
                    tweak,
                    vout_data,
                });
            }
        }

        None
    }

    pub fn to_be_bytes(self) -> Vec<u8> {
        let mut data = vec![];
        data.extend_from_slice(&self.txid.as_ref());
        data.extend_from_slice(&self.tweak.serialize());

        let vout_data = self.vout_data;

        data.extend_from_slice(&vout_data.len().to_be_bytes());

        for vout in vout_data {
            data.extend_from_slice(&vout.vout.to_be_bytes());
            data.extend_from_slice(&vout.amount.to_be_bytes());
            data.extend_from_slice(&vout.script_pub_key.as_bytes());
        }

        data
    }
}

#[derive(Clone, Debug)]
pub struct TweakBlockData {
    pub block_height: u64,
    pub tx_data: Vec<TweakData>,
}

impl TweakBlockData {
    pub fn new(block_height: u64) -> Self {
        Self {
            block_height,
            tx_data: vec![],
        }
    }

    pub fn from_boxed_slice(key: Box<[u8]>, data: Box<[u8]>) -> Self {
        let data = data.into_vec();

        let block_height_bytes = &key[..];
        let mut block_height = [0u8; 8];
        block_height.copy_from_slice(&block_height_bytes);
        let block_height = u64::from_be_bytes(block_height);

        let mut result = Self::new(block_height);
        let mut chunk = 0;

        while data.len() > chunk {
            if let Some(tweak_data) =
                TweakData::from_boxed_slice(data.clone().into_boxed_slice(), &mut chunk)
            {
                result.tx_data.push(tweak_data);
            }
        }

        result
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        let mut data = vec![];
        data.extend_from_slice(&self.block_height.to_be_bytes());
        for tweak in self.tx_data {
            data.extend_from_slice(&tweak.to_be_bytes());
        }

        data.into_boxed_slice()
    }
}
