//! PVUGC witness extraction - data structures only
//!
//! The actual logging happens inline in perform_verification() (lib.rs)
//! with feature-gated hooks. This module just defines the data structure.

#![cfg(feature = "pvugc-hooks")]

use alloc::vec::Vec;
use math::FieldElement;

/// PVUGC witness log extracted from STARK verification
pub struct PvugcLog<E: FieldElement> {
    pub z: E,                              // OOD point ζ
    pub zeta: Option<E>,                   // Optional OOD point for extractors expecting Option
    pub query_positions: Vec<usize>,       // Query indices in LDE domain
    pub ood_evals_merged: Vec<E>,          // Merged OOD evaluations
    pub deep_evaluations: Vec<E>,          // DEEP composition per query (comp_claim)
    pub x_points: Vec<E>,                  // LDE x coordinates per query
    pub comp_claims: Vec<E>,               // Alias for deep_evaluations (compat)
    // Per FRI layer: per-query fold values
    pub fri_layers: Vec<Vec<FriFold<E>>>,
    // Strict DEEP per-query components: flattened per-term vectors matching composer order
    pub deep_strict_per_query: Vec<DeepStrictPerQuery<E>>,
}

impl<E: FieldElement> PvugcLog<E> {
    pub fn new() -> Self {
        Self {
            z: E::ZERO,
            zeta: None,
            query_positions: Vec::new(),
            ood_evals_merged: Vec::new(),
            deep_evaluations: Vec::new(),
            x_points: Vec::new(),
            comp_claims: Vec::new(),
            fri_layers: Vec::new(),
            deep_strict_per_query: Vec::new(),
        }
    }
}

impl<E: FieldElement> Default for PvugcLog<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Per-layer, per-query FRI fold triple
pub struct FriFold<E: FieldElement> {
    pub v_lo: E,
    pub v_hi: E,
    pub v_next: E,
}

/// Strict DEEP components per query matching composer order
pub struct DeepStrictPerQuery<E: FieldElement> {
    pub coeffs: Vec<E>,   // γ_i flattened to match terms
    pub ox: Vec<E>,       // T_i(x) per term
    pub oz: Vec<E>,       // T_i(z or z*g) per term
    pub z_mults: Vec<E>,  // multipliers so denom is (x - ζ * z_mults[i])
}
