//! SP1 Public Inputs for PVUGC
//!
//! SP1's Groth16 wrapper has 2 public inputs:
//! - vkey_hash: Poseidon2(BabyBear) of program VK → converted to Fr (248 bits)
//! - committed_values_digest: SHA256(public_outputs) with top 4 bits zeroed (252 bits)
//!
//! PVUGC can handle multiple public inputs directly - no hashing needed!
//! The outer circuit takes [vkey_hash, committed_values_digest] as public inputs.
//!
//! The `armed_digest` functions are kept for backwards compatibility but the
//! recommended approach is to use `Sp1PublicInputs` directly.

use ark_bls12_377::Fr as Fr377;


/// SP1's public inputs (what SP1's Groth16 wrapper constrains)
/// 
/// Use this directly as the inner_public_inputs for OuterCircuit.
/// PVUGC handles 2 public inputs natively - no hashing needed.
#[derive(Clone, Debug)]
pub struct Sp1PublicInputs {
    /// Hash of the SP1 program's verification key (Poseidon2 in BabyBear, ~248 bits)
    pub vkey_hash: Fr377,
    /// Hash of the program's public outputs (SHA256, top 4 bits zeroed, ~252 bits)
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

