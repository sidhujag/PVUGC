//! One-Sided GS PVUGC for Groth16
//!
//! This crate implements the coefficient-carrying one-sided GS approach
//! that achieves all PVUGC properties:
//! - Deposit-only arming (statement-only G₂ arms)
//! - Permissionless decap (no committee at spend)
//! - Proof-agnostic (K = R^ρ for any valid proof)
//! - Witness-independent (R depends only on vk, vault_utxo)
//! - SNARK-gated (requires valid Groth16)
//!
//! Architecture:
//! 1. Groth16 proves statement: i.e. Bitcoin light client
//! 2. Prover exposes MSM coefficients b_j, c_i
//! 3. One-sided GS PPE: ∏ e(X^(B)_j, Y_j) · e(C, -δ) = R(vk,x)
//! 4. All G₂ bases from VK (statement-only!)
//! 5. Arm: Y_j^ρ, δ^ρ
//! 6. Decap: K = R^ρ

pub mod arming;
pub mod coeff_recorder;
pub mod dlrep;
pub mod ppe;
pub mod decap;
pub mod ctx;
pub mod poce;
pub mod api;

// Re-exports - Public API
pub use arming::{RowBases, Arms, arm_rows, build_row_bases_from_vk};
pub use coeff_recorder::{CoefficientRecorder, BCoefficients, SimpleCoeffRecorder};
pub use dlrep::{DlrepBProof, DlrepTieProof, prove_b_msm, verify_b_msm, prove_tie_aggregated, verify_tie_aggregated};
pub use ppe::{compute_groth16_target, build_one_sided_ppe, extract_y_bases, derive_gamma_rademacher, PvugcVk};
pub use decap::{decap_one_sided, OneSidedCommitments};
pub use poce::{PoceAcrossProof, prove_poce_across, verify_poce_across};
pub use api::{OneSidedPvugc, PvugcBundle};
