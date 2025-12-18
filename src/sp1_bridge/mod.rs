//! SP1 Bridge for PVUGC
//!
//! This module provides the bridge between SP1's Groth16 proofs (from gnark)
//! and PVUGC's outer circuit. The approach:
//!
//! 1. SP1 (with gnark forked to BLS12-377) produces a Groth16 proof
//! 2. This module deserializes the gnark proof into arkworks types
//! 3. Exposes SP1's two public inputs: (vkey_hash, committed_values_digest)
//! 4. The outer circuit verifies the inner proof against these public inputs
//!
//! PVUGC supports multiple public inputs natively, so no extra hashing is required.
//!
//! ## Universal Groth16 VK
//!
//! The SP1 Groth16 wrapper circuit is **universal** - the same VK works for all programs.
//! The VK is stored in `sp1-keys/` and loaded at compile time:
//! - `sp1-keys/test/groth16_vk.bin` - For testing (smaller params)
//! - `sp1-keys/production/groth16_vk.bin` - For production (full security)

mod gnark_deserialize;
mod armed_digest;

pub use gnark_deserialize::{
    Sp1Groth16Proof,
    Sp1VerifyingKey,
    parse_gnark_proof_bls12_377,
    parse_gnark_vk_bls12_377,
    parse_arkworks_vk_bls12_377,
    decode_sp1_proof_hex,
    decode_sp1_public_input,
};

pub use armed_digest::{
    Sp1PublicInputs,
    compute_inner_vk_hash,
};

use ark_bls12_377::{Bls12_377, Fr as Fr377};
use ark_groth16::{Proof, VerifyingKey};
use once_cell::sync::Lazy;

/// Universal SP1 Groth16 VK bytes (production params)
/// 
/// This is the same VK for ALL SP1 programs on BLS12-377.
/// Generated once during trusted setup, then baked in.
#[cfg(feature = "sp1-production-vk")]
pub static SP1_GROTH16_VK_BYTES: &[u8] = include_bytes!("../../sp1-keys/production/groth16_vk.bin");

/// Universal SP1 Groth16 VK bytes (test params)
#[cfg(not(feature = "sp1-production-vk"))]
pub static SP1_GROTH16_VK_BYTES: &[u8] = &[]; // Placeholder until keys are generated

/// Lazily parsed universal SP1 Groth16 VK
/// 
/// Returns None if keys haven't been generated yet
pub static SP1_GROTH16_VK: Lazy<Option<VerifyingKey<Bls12_377>>> = Lazy::new(|| {
    if SP1_GROTH16_VK_BYTES.is_empty() {
        None
    } else {
        parse_gnark_vk_bls12_377(SP1_GROTH16_VK_BYTES).ok()
    }
});

/// Get the universal SP1 Groth16 VK
/// 
/// # Panics
/// Panics if keys haven't been generated. Run SP1 trusted setup first.
pub fn get_sp1_vk() -> &'static VerifyingKey<Bls12_377> {
    SP1_GROTH16_VK.as_ref().expect(
        "SP1 Groth16 VK not available. Run trusted setup: \
        cd /path/to/syscoin/sp1 && cargo run -p sp1-prover --release --bin build_groth16_bn254 --features native-gnark -- --build-dir /path/to/PVUGC/sp1-keys/production"
    )
}

/// Check if SP1 keys have been generated
pub fn sp1_keys_available() -> bool {
    !SP1_GROTH16_VK_BYTES.is_empty() && SP1_GROTH16_VK.is_some()
}

/// The complete SP1 proof bundle ready for PVUGC integration
#[derive(Clone)]
pub struct Sp1ProofBundle {
    /// The deserialized Groth16 proof (A, B, C points)
    pub proof: Proof<Bls12_377>,
    
    /// SP1 wrapper's verification key (universal, fixed for all programs)
    pub inner_vk: VerifyingKey<Bls12_377>,
    
    /// SP1's public inputs (vkey_hash + committed_values_digest)
    pub public_inputs: Sp1PublicInputs,
}

impl Sp1ProofBundle {
    /// Create a new SP1 proof bundle from raw gnark outputs with explicit VK
    pub fn from_gnark(
        raw_proof: &[u8],
        raw_vk: &[u8],
        vkey_hash: Fr377,
        committed_values_digest: Fr377,
    ) -> Result<Self, Sp1BridgeError> {
        let proof = parse_gnark_proof_bls12_377(raw_proof)?;
        let inner_vk = parse_gnark_vk_bls12_377(raw_vk)?;
        
        Ok(Self {
            proof,
            inner_vk,
            public_inputs: Sp1PublicInputs::new(vkey_hash, committed_values_digest),
        })
    }
    
    /// Create a new SP1 proof bundle using the baked-in universal VK
    /// 
    /// This is the preferred method for production - uses the pre-generated
    /// universal Groth16 VK from sp1-keys/
    /// 
    /// # Arguments
    /// * `raw_proof` - The raw proof bytes from SP1 (skip 4-byte vkey prefix from proof.bytes())
    /// * `vkey_hash` - SP1 program's vkey hash (from SP1VerifyingKey.bytes32())
    /// * `committed_values_digest` - Hash of program's public outputs
    pub fn from_proof(
        raw_proof: &[u8],
        vkey_hash: Fr377,
        committed_values_digest: Fr377,
    ) -> Result<Self, Sp1BridgeError> {
        let proof = parse_gnark_proof_bls12_377(raw_proof)?;
        let inner_vk = get_sp1_vk().clone();
        
        Ok(Self {
            proof,
            inner_vk,
            public_inputs: Sp1PublicInputs::new(vkey_hash, committed_values_digest),
        })
    }
    
    /// Get the public inputs for the outer circuit (2 values)
    /// 
    /// Returns [vkey_hash, committed_values_digest] - PVUGC handles both directly.
    pub fn inner_public_inputs(&self) -> Vec<Fr377> {
        self.public_inputs.to_vec()
    }
    
    /// Get vkey_hash (identifies which SP1 program)
    pub fn vkey_hash(&self) -> Fr377 {
        self.public_inputs.vkey_hash
    }
    
    /// Get committed_values_digest (hash of program outputs)
    pub fn committed_values_digest(&self) -> Fr377 {
        self.public_inputs.committed_values_digest
    }
}

/// Errors that can occur in SP1 bridge operations
#[derive(Debug, Clone)]
pub enum Sp1BridgeError {
    /// Invalid proof format
    InvalidProofFormat(String),
    /// Invalid verification key format
    InvalidVkFormat(String),
    /// Deserialization error
    DeserializationError(String),
}

impl std::fmt::Display for Sp1BridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProofFormat(s) => write!(f, "Invalid proof format: {}", s),
            Self::InvalidVkFormat(s) => write!(f, "Invalid VK format: {}", s),
            Self::DeserializationError(s) => write!(f, "Deserialization error: {}", s),
        }
    }
}

impl std::error::Error for Sp1BridgeError {}

