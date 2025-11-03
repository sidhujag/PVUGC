//! One-Sided GS PVUGC for Groth16
//!
//! This crate implements the coefficient-carrying one-sided GS approach
//! for efficient PVUGC operations on Groth16 proofs.
//!
//! Properties:
//! - Deposit-only arming (statement-only G₂ arms from VK)
//! - Permissionless decap (no committee at spend)
//! - Proof-agnostic (K = R^ρ for any valid proof of same statement)
//! - Witness-independent (R depends only on vk, public_inputs)
//! - SNARK-gated (requires valid Groth16 proof)
//!
//! The crate also includes demonstration modules for recursive proof-of-proof
//! architectures that could provide constant-size scalability. See the
//! test_recursive_demo test for details.

pub mod arming;
pub mod coeff_recorder;
pub mod dlrep;
pub mod ppe;
pub mod decap;
pub mod ctx;
pub mod poce;
pub mod api;
pub mod error;
pub mod ct;
pub mod io;
pub mod bitcoin;  // Bitcoin integration module (new)

// Recursive demonstration modules (not for production use)
// These modules demonstrate how PVUGC could work with proof-of-proof recursion
// for constant-size scalability. They are kept for educational/testing purposes.
pub mod outer_compressed;
pub mod pvugc_outer;

// Test utilities (available in both unit tests and integration tests)
pub mod test_circuits; // Shared test circuits
pub mod test_fixtures;  // Shared fixtures with disk caching

// Inner STARK verifier (hybrid) in a single module
pub mod inner_stark;
pub mod host_api;
pub mod fs;
pub mod witness;
pub use fs::transcript::assemble_transcript_bytes;
pub use fs::transcript::{TranscriptBuilder, TailBuilder, WinterfellTailMeta, build_winterfell_tail, build_tail_from_proof_bytes, derive_fri_layers, fr377_to_le48, flatten_roots, flatten_roots_32};
#[cfg(feature = "serde")]
pub use fs::transcript::build_tail_from_proof_serde;

// Crypto helpers (Poseidon params + host Merkle helpers)
pub mod crypto {
    pub mod poseidon_fr377_t3;
    pub mod poseidon_merkle_helpers;
}

// Re-exports - Public API
pub use arming::{ColumnBases, ColumnArms, arm_columns};
pub use coeff_recorder::{CoefficientRecorder, BCoefficients, SimpleCoeffRecorder};
pub use dlrep::{
    DlrepBProof,
    DlrepPerColumnTies,
    prove_b_msm,
    verify_b_msm,
    prove_ties_per_column,
    verify_ties_per_column,
};
pub use ppe::{compute_groth16_target, build_one_sided_ppe, extract_y_bases, PvugcVk};
pub use decap::OneSidedCommitments;
pub use poce::{PoceColumnProof, prove_poce_column, verify_poce_column};
pub use api::{OneSidedPvugc, PvugcBundle};

// Recursive demonstration types (not for production use)
// These are exposed for testing and educational purposes only.
// Production code should use the main API (OneSidedPvugc).
pub use outer_compressed::{
    cycles::{Bls12Bw6Cycle, Mnt4Mnt6Cycle},
    fr_inner_to_outer,
    fr_inner_to_outer_for,
    prove_outer,
    prove_outer_for,
    setup_outer_params,
    setup_outer_params_for,
    verify_outer,
    verify_outer_for,
    DefaultCycle,
    InnerE,
    InnerFr,
    OuterE,
    OuterFr,
    RecursionCycle,
};

// Test utilities re-exports
pub use test_circuits::AddCircuit;
pub use test_fixtures::{get_fixture, get_fixture_mnt, DefaultFixture, GlobalFixture, MntFixture};

// Public exports for the inner STARK verifier circuit helpers
pub use inner_stark::{
    HybridQueryWitness,
    InnerStarkVerifierCircuit,
    setup_inner_stark,
    prove_inner_stark,
    verify_inner_stark,
    compute_inner_public_inputs,
};
pub use host_api::prove_outer_with_inner;
