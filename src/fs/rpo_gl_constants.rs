//! RPO (Rescue Prime Optimized) over Goldilocks (Rp64_256) constants adapter
//!
//! We reference the constants directly from the pinned Winterfell crate to avoid duplication.
//! Pin Winterfell in Cargo.toml to a specific version or commit to keep FS bit-for-bit stable.

use winter_crypto::hashers::Rp64_256;

/// State width for Rp64_256 as defined by Winterfell.
#[inline]
pub fn rpo_state_width() -> usize {
    Rp64_256::STATE_WIDTH
}

/// Total number of Rescue rounds in Rp64_256 as defined by Winterfell.
#[inline]
pub fn rpo_num_rounds() -> usize {
    Rp64_256::NUM_ROUNDS
}

/// Return ARK1 round constants as u64 rows (Goldilocks elements as integers).
pub fn rpo_ark1_rows_u64() -> Vec<Vec<u64>> {
    Rp64_256::ARK1
        .iter()
        .map(|row| row.iter().map(|e| e.as_int()).collect::<Vec<u64>>())
        .collect::<Vec<Vec<u64>>>()
}

/// Return ARK2 round constants as u64 rows (Goldilocks elements as integers).
pub fn rpo_ark2_rows_u64() -> Vec<Vec<u64>> {
    Rp64_256::ARK2
        .iter()
        .map(|row| row.iter().map(|e| e.as_int()).collect::<Vec<u64>>())
        .collect::<Vec<Vec<u64>>>()
}

/// Return MDS matrix as u64 rows (Goldilocks elements as integers).
pub fn rpo_mds_rows_u64() -> Vec<Vec<u64>> {
    Rp64_256::MDS
        .iter()
        .map(|row| row.iter().map(|e| e.as_int()).collect::<Vec<u64>>())
        .collect::<Vec<Vec<u64>>>()
}

/// Rescue S-box exponent alpha for Rp64_256 over Goldilocks
#[inline]
pub fn rpo_alpha() -> u64 { 7 }

/// Rescue inverse S-box exponent alpha^{-1} mod (p-1) for Goldilocks
#[inline]
pub fn rpo_inv_alpha() -> u64 { 10540996611094048183 }


