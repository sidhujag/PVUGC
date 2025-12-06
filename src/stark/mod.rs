//! STARK verifier modules for inner circuit validation
//!
//! This module contains the full STARK verifier implementation including:
//! - Goldilocks field arithmetic (gl_u64)
//! - FRI gadgets for low-degree testing
//! - Merkle proof verification
//! - Full AIR constraint checking
//! - Poseidon hash function implementation

pub mod gadgets;
pub mod gl_u64;
pub mod inner_stark_full;
pub mod stark_proof_parser;

// Crypto helpers (Poseidon params + host Merkle helpers)
pub mod crypto {
    pub mod poseidon_fr377_t3;
    pub mod poseidon_merkle_helpers;
}

/// STARK circuits currently target the original BLS12-377 field regardless of the
/// recursion cycle used by the outer circuit.
pub type StarkInnerFr = ark_bls12_377::Fr;

// Re-export main types
pub use inner_stark_full::{
    AirParams, CompQuery, FullStarkVerifierCircuit, TraceQuery, TraceSegmentWitness,
};

#[cfg(test)]
pub mod test_utils;

// Tests module (internal tests for STARK components)
#[cfg(test)]
mod tests {
    mod full_stark_verifier_smoke;
    mod gl_fast_unit_tests;
    mod poseidon_merkle_selfcheck;
    mod stark_verifier_comprehensive;

    pub(crate) mod helpers {
        pub(crate) mod rpo_compatibility;
        pub(crate) mod simple_vdf;
    }
}
