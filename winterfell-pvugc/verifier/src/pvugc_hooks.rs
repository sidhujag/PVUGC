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
    // Optional: RPO Merkle data and commitments for LDE trace/comp and FRI roots
    pub trace_lde_root_le_32: Option<[u8;32]>,
    pub comp_lde_root_le_32: Option<[u8;32]>,
    pub fri_layer_roots_le_32: Vec<[u8;32]>,
    pub trace_paths_nodes_le_32: Vec<Vec<[u8;32]>>,
    pub trace_paths_pos: Vec<Vec<bool>>,
    pub comp_paths_nodes_le_32: Vec<Vec<[u8;32]>>,
    pub comp_paths_pos: Vec<Vec<bool>>,
    pub ood_commitment_le: Vec<u8>,
    // Optional: leaf digests per query (32-byte each) for trace and composition
    pub trace_leaf_digests_le_32: Vec<[u8;32]>,
    pub comp_leaf_digests_le_32: Vec<[u8;32]>,
    // FRI per-layer logs
    pub fri_layer_positions: Vec<Vec<usize>>,           // per-layer queried positions
    pub fri_layer_leaf_digests_le_32: Vec<Vec<[u8;32]>>, // per-layer leaf digests (commitment leaves)
    pub fri_layer_paths_nodes_le_32: Vec<Vec<[u8;32]>>,  // flattened nodes per layer (batch nodes)
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
            trace_lde_root_le_32: None,
            comp_lde_root_le_32: None,
            fri_layer_roots_le_32: Vec::new(),
            trace_paths_nodes_le_32: Vec::new(),
            trace_paths_pos: Vec::new(),
            comp_paths_nodes_le_32: Vec::new(),
            comp_paths_pos: Vec::new(),
            ood_commitment_le: Vec::new(),
            trace_leaf_digests_le_32: Vec::new(),
            comp_leaf_digests_le_32: Vec::new(),
            fri_layer_positions: Vec::new(),
            fri_layer_leaf_digests_le_32: Vec::new(),
            fri_layer_paths_nodes_le_32: Vec::new(),
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
