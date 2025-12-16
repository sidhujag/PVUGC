//! STARK verifier modules for inner circuit validation
//!
//! This module contains the full STARK verifier implementation including:
//! - Goldilocks field arithmetic (gl_u64)
//! - FRI gadgets for low-degree testing
//! - Merkle proof verification
//! - Full AIR constraint checking
//! - Poseidon hash function implementation

pub mod aggregator_air;
pub mod gadgets;
pub mod gl_u64;
pub mod inner_stark_full;
pub mod ood_eval_r1cs;
pub mod stark_proof_parser;
pub mod verifier_air;
pub mod verifier_stark_groth16;

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
    AirParams, CompQuery, FullStarkVerifierCircuit, TraceQuery,
    TraceSegmentWitness, AGGREGATOR_VERSION,
};

// Re-export Aggregator STARK types (two-AIR design: AggregatorAir -> VerifierAir -> Groth16).
pub use aggregator_air::{
    AggregatorAir, AggregatorConfig, AggregatorProver, AggregatorPublicInputs,
    ChildStatementHash, generate_aggregator_proof, generate_aggregator_proof_with_config,
    AGGREGATOR_TRACE_WIDTH,
};

// Re-export Verifier STARK integration types
pub use verifier_stark_groth16::{
    prove_verifier_stark,
    VerifierStarkResult,
};

#[cfg(test)]
pub mod test_utils;

// Tests module (internal tests for STARK components)
#[cfg(test)]
mod tests {
    mod full_stark_verifier_smoke;
    mod gl_fast_unit_tests;
    mod poseidon_merkle_selfcheck;
    mod recursive_stark_e2e;
    mod stark_verifier_comprehensive;

    pub(crate) mod helpers {
        pub(crate) mod add2;
        pub(crate) mod cubic_fib;
        pub(crate) mod rpo_compatibility;
        pub(crate) mod simple_vdf;
    }
}
