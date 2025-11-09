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

pub mod api;
pub mod arming;
pub mod bitcoin;
pub mod coeff_recorder;
pub mod ct;
pub mod ctx;
pub mod decap;
pub mod dlrep;
pub mod error;
pub mod io;
pub mod poce;
pub mod ppe; // Bitcoin integration module (new)

// Recursive demonstration modules (not for production use)
// These modules demonstrate how PVUGC could work with proof-of-proof recursion
// for constant-size scalability. They are kept for educational/testing purposes.
pub mod outer_compressed;
pub mod pvugc_outer;

// Test utilities (available in both unit tests and integration tests)
pub mod test_circuits; // Shared test circuits
pub mod test_fixtures; // Shared fixtures with disk caching

// Inner STARK verifier modules
pub mod inner_stark_full; // Full verifier approach
pub mod stark_proof_parser; // Parser for full verifier (no hooks!)
pub use inner_stark_full::{
    AirParams, CompQuery, FullStarkVerifierCircuit, TraceQuery, TraceSegmentWitness,
};
pub mod gadgets;
pub mod gl_u64; // Goldilocks u64 arithmetic (for witness computation)

// Crypto helpers (Poseidon params + host Merkle helpers)
pub mod crypto {
    pub mod poseidon_fr377_t3;
    pub mod poseidon_merkle_helpers;
}

// Re-exports - Public API
pub use api::{OneSidedPvugc, PvugcBundle};
pub use arming::{arm_columns, ColumnArms, ColumnBases};
pub use coeff_recorder::{BCoefficients, CoefficientRecorder, SimpleCoeffRecorder};
pub use decap::OneSidedCommitments;
pub use dlrep::{
    prove_b_msm, prove_ties_per_column, verify_b_msm, verify_ties_per_column, DlrepBProof,
    DlrepPerColumnTies,
};
pub use poce::{prove_poce_column, verify_poce_column, PoceColumnProof};
pub use ppe::{build_one_sided_ppe, compute_groth16_target, extract_y_bases, PvugcVk};

// Recursive demonstration types (not for production use)
// These are exposed for testing and educational purposes only.
// Production code should use the main API (OneSidedPvugc).
pub use outer_compressed::{
    cycles::{Bls12Bw6Cycle, Mnt4Mnt6Cycle},
    fr_inner_to_outer, fr_inner_to_outer_for, prove_outer, prove_outer_for, setup_outer_params,
    setup_outer_params_for, verify_outer, verify_outer_for, DefaultCycle, InnerE, InnerFr, OuterE,
    OuterFr, RecursionCycle,
};

// Test utilities re-exports
pub use test_circuits::AddCircuit;
pub use test_fixtures::{get_fixture, get_fixture_mnt, DefaultFixture, GlobalFixture, MntFixture};
