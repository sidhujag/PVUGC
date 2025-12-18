//! SP1 Public Inputs for PVUGC
//!
//! SP1's Groth16 wrapper has 2 public inputs:
//! - vkey_hash: Poseidon2(BabyBear) of program VK → converted to Fr (253 bits)
//! - committed_values_digest: SHA256(public_outputs) with top 3 bits zeroed (253 bits)
//!
//! PVUGC can handle multiple public inputs directly - no hashing needed!
//! The outer circuit takes [vkey_hash, committed_values_digest] as public inputs.
//!
//! The `armed_digest` functions are kept for backwards compatibility but the
//! recommended approach is to use `Sp1PublicInputs` directly.

use ark_bls12_377::{Bls12_377, Fr as Fr377};
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonSponge, PoseidonConfig},
    CryptographicSponge,
};
use ark_ff::PrimeField;
use ark_groth16::VerifyingKey;
use ark_serialize::CanonicalSerialize;

use crate::stark::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;

/// SP1's public inputs (what SP1's Groth16 wrapper constrains)
/// 
/// Use this directly as the inner_public_inputs for OuterCircuit.
/// PVUGC handles 2 public inputs natively - no hashing needed.
#[derive(Clone, Debug)]
pub struct Sp1PublicInputs {
    /// Hash of the SP1 program's verification key (Poseidon2 in BabyBear, ~253 bits)
    pub vkey_hash: Fr377,
    /// Hash of the program's public outputs (SHA256, top 3 bits zeroed, ~253 bits)
    pub committed_values_digest: Fr377,
}

impl Sp1PublicInputs {
    /// Create from raw values
    pub fn new(vkey_hash: Fr377, committed_values_digest: Fr377) -> Self {
        Self { vkey_hash, committed_values_digest }
    }
    
    /// Convert to vector for outer circuit (recommended approach)
    pub fn to_vec(&self) -> Vec<Fr377> {
        vec![self.vkey_hash, self.committed_values_digest]
    }
    
    /// Get as slice for outer circuit
    pub fn as_slice(&self) -> [Fr377; 2] {
        [self.vkey_hash, self.committed_values_digest]
    }
}

/// Compute a hash of the inner verification key.
///
/// This is used to bind the specific SP1 wrapper setup (universal for all programs).
/// The hash is computed by serializing the VK and hashing with Poseidon.
pub fn compute_inner_vk_hash(inner_vk: &VerifyingKey<Bls12_377>) -> Fr377 {
    // Serialize the VK to bytes
    let mut vk_bytes = Vec::new();
    inner_vk.serialize_compressed(&mut vk_bytes)
        .expect("VK serialization should not fail");
    
    // Convert bytes to field elements and hash
    // We chunk the bytes and interpret each chunk as a field element
    let config: &PoseidonConfig<Fr377> = &POSEIDON377_PARAMS_T3_V1;
    let mut sponge = PoseidonSponge::new(config);
    
    // Add domain separator
    let domain = Fr377::from_be_bytes_mod_order(b"SP1-VK-HASH-v1\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    sponge.absorb(&domain);
    
    // Hash the VK bytes in chunks
    for chunk in vk_bytes.chunks(31) {
        let mut padded = [0u8; 32];
        padded[..chunk.len()].copy_from_slice(chunk);
        let fe = Fr377::from_le_bytes_mod_order(&padded);
        sponge.absorb(&fe);
    }
    
    let result: Vec<Fr377> = sponge.squeeze_field_elements(1);
    result[0]
}


