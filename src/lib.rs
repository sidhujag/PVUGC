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

pub mod adaptor_ve;
pub mod api;
pub mod arming;
pub mod bitcoin;
pub mod ct;
pub mod ctx;
pub mod decap;
pub mod error;
pub mod io;
pub mod poce;
pub mod poseidon_fr381_t3;
pub mod ppe; // Bitcoin integration module (new)
pub mod prover_lean;
pub mod secp256k1; // Lean Prover module

// Recursive demonstration modules (not for production use)
// These modules demonstrate how PVUGC could work with proof-of-proof recursion
// for constant-size scalability. They are kept for educational/testing purposes.
pub mod outer_compressed;
pub mod pvugc_outer;

// Test utilities (available in both unit tests and integration tests)
pub mod test_circuits; // Shared test circuits
pub mod test_fixtures; // Shared fixtures with disk caching

// SP1 Bridge: Simplified integration for gnark proofs → PVUGC
pub mod sp1_bridge;

// Re-exports - Public API
pub use adaptor_ve::{prove_adaptor_ve, verify_adaptor_ve, AdaptorVeProof};
pub use api::{ColumnArmingAttestation, OneSidedPvugc, PvugcBundle};
pub use arming::{arm_columns, ColumnArms, ColumnBases};
pub use decap::{build_commitments, OneSidedCommitments};
pub use decap::prove_and_build_commitments;
pub use poce::{prove_poce_column, verify_poce_column, PoceColumnProof};
pub use ppe::{
    build_one_sided_ppe, compute_baked_target, compute_groth16_target, extract_y_bases, PvugcVk,
};
pub use prover_lean::{prove_lean, LeanProvingKey};

// Recursive demonstration types (not for production use)
// These are exposed for testing and educational purposes only.
// Production code should use the main API (OneSidedPvugc).
pub use outer_compressed::{
    cycles::{Bls12Bw6Cycle, Mnt4Mnt6Cycle},
    fr_inner_to_outer, fr_inner_to_outer_for, prove_outer, prove_outer_for, setup_outer_params,
    setup_outer_params_for, verify_outer, verify_outer_for, DefaultCycle, InnerE, InnerFr, OuterE,
    OuterFr, RecursionCycle, OuterCircuit,
};

// Test utilities re-exports
pub use test_circuits::AddCircuit;
pub use test_fixtures::{
    get_fixture, get_fixture_bls, get_fixture_mnt, BlsFixture, DefaultFixture, GlobalFixture,
    MntFixture,
};
