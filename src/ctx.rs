//! Context Binding for PVUGC
//!
//! Cryptographic context that binds all components together

use sha2::{Sha256, Digest};

/// Context for PVUGC deployment
#[derive(Clone, Debug)]
pub struct PvugcContext {
    /// Vault UTXO (txid, output_index)
    pub vault_utxo: Vec<u8>,
    
    /// Wrapper VK digest
    pub vk_digest: [u8; 32],
    
    /// CRS digests
    pub crs_digests: Vec<[u8; 32]>,
    
    /// Epoch/chain identifiers
    pub epoch: u64,
}

impl PvugcContext {
    pub fn to_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"PVUGC_CTX_v1");
        hasher.update(&self.vault_utxo);
        hasher.update(&self.vk_digest);
        for digest in &self.crs_digests {
            hasher.update(digest);
        }
        hasher.update(&self.epoch.to_le_bytes());
        
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }
}

