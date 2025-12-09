//! Full STARK Verifier Circuit
//!
//! This module implements a complete Winterfell STARK verifier as an arkworks R1CS circuit.
//!
//! ## Design Principles:
//!
//! 1. **Direct verification**: Parse Winterfell proof and verify in-circuit
//! 2. **Native GL arithmetic**: All DEEP/FRI operations in Goldilocks field  
//! 3. **Light RPO-256**: Congruence-only internally, canonicalize at byte boundaries
//! 4. **RPO-256 Merkle**: Verify Winterfell's actual commitments (no shadow trees)
//! 5. **One source of truth**: The proof bytes, not extracted witnesses
//!
//! ## Circuit Flow:
//!
//! ```text
//! Inputs: proof_bytes, public_inputs, air_params
//!   ↓
//! 1. Parse: Extract commitments, queries, OOD frame, FRI proof
//!   ↓
//! 2. Merkle: Verify trace_queries against trace_commitment (RPO-256)
//!   ↓
//! 3. DEEP: Compute composition from queries + OOD (native GL)
//!   ↓
//! 4. FRI: Verify multi-layer folding + Merkle commitments
//!   ↓
//! 5. FS: Derive challenges in-circuit, verify consistency
//! ```

use super::gadgets::rpo_gl_light::canonicalize_to_bytes;
use crate::stark::StarkInnerFr as InnerFr;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::cmp::CmpGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::uint64::UInt64 as UInt64Var;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
// Light RPO for internal operations, canonicalize only at serialization boundaries
use super::gadgets::gl_fast::{
    gl_add_light, gl_batch_inv_light, gl_mul_light, gl_sub_light, GlVar,
};
use super::gadgets::gl_range::{gl_alloc_u64, gl_alloc_u64_vec};
use super::gadgets::utils::CombinerKind;
// OOD verification is now in ood_eval_r1cs.rs
use super::ood_eval_r1cs::verify_ood_equation_in_circuit;

// Use GL type alias for non-native Goldilocks operations in Fr377
pub type FpGLVar = FpVar<InnerFr>;
type UInt64GLVar = UInt64Var<InnerFr>;

/// Current aggregator STARK version
pub const AGGREGATOR_VERSION: u64 = 1;

/// AIR parameters needed for verification (constants, not witnesses)
///
/// In the recursive STARK architecture, these parameters describe the
/// FINAL proof that Groth16 verifies (i.e., the Verifier STARK output).
/// For now, they also describe application STARKs directly.
#[derive(Clone, Debug)]
pub struct AirParams {
    pub trace_width: usize,
    pub comp_width: usize,
    pub trace_len: usize,
    pub lde_blowup: usize,
    pub num_queries: usize,
    pub fri_folding_factor: usize,
    pub fri_num_layers: usize,
    pub lde_generator: u64, // LDE domain generator (e.g., 8 for size 64)
    pub domain_offset: u64, // Domain offset (e.g., 7 for Goldilocks)
    pub g_lde: u64,         // Same as lde_generator
    pub g_trace: u64,       // Trace domain generator (e.g., 2^24 for trace_len=8)
    pub combiner_kind: CombinerKind,
    pub fri_terminal: super::gadgets::fri::FriTerminalKind,
    pub num_constraint_coeffs: usize,
    pub grinding_factor: u32,
    /// Aggregator STARK version (allows protocol upgrades).
    /// In recursive mode: this is the version of the Verifier STARK.
    pub aggregator_version: u64,
}

/// Full STARK verifier circuit
///
/// Verifies a Winterfell STARK proof completely in-circuit.
/// Proof is parsed on host, structured data passed to circuit.
#[derive(Clone)]
pub struct FullStarkVerifierCircuit {
    // Public input: Single hash binding all commitments + public inputs
    pub statement_hash: InnerFr, // Poseidon(trace_root || comp_root || fri_roots || ood_commit || pub_inputs)

    // STARK public inputs (to bind into statement hash)
    pub stark_pub_inputs: Vec<u64>, // STARK's public inputs

    // Fiat-Shamir context seed (for transcript alignment)
    pub fs_context_seed_gl: Vec<u64>, // proof.context.to_elements().as_int()

    // Commitments (witness, but bound to public hash)
    pub trace_commitment_le32: Vec<[u8; 32]>,
    pub comp_commitment_le32: [u8; 32],
    pub fri_commitments_le32: Vec<[u8; 32]>, // One per FRI layer
    pub ood_commitment_le32: [u8; 32],       // Binds OOD frame to prevent free witnesses

    // Query openings (witness)
    pub query_positions: Vec<usize>, // LDE domain positions
    pub pow_nonce: u64,              // PoW nonce used to salt query seed
    pub trace_segments: Vec<TraceSegmentWitness>, // Per-segment openings + Merkle metadata
    pub comp_queries: Vec<CompQuery>, // Per-query composition openings

    pub comp_batch_nodes: Vec<Vec<[u8; 32]>>,
    pub comp_batch_depth: u8,
    pub comp_batch_indexes: Vec<usize>,

    // OOD frame (witness)
    pub ood_trace_current: Vec<u64>, // Trace at z (GL values)
    pub ood_trace_next: Vec<u64>,    // Trace at z·g
    pub ood_comp: Vec<u64>,          // Composition at z
    pub ood_comp_next: Vec<u64>,     // Composition at z·g (for LINEAR batching)

    // FRI proof (witness)
    pub fri_layers: Vec<FriLayerQueries>, // Per-layer fold data

    // FRI remainder coefficients (empty when terminal = Constant)
    pub fri_remainder_coeffs: Vec<u64>,

    // AIR parameters (constants)
    pub air_params: AirParams,
}

/// Single trace query opening
#[derive(Clone, Debug)]
pub struct TraceQuery {
    pub values: Vec<u64>,           // GL field elements (LDE row)
    pub merkle_path: Vec<[u8; 32]>, // RPO-256 sibling nodes
    pub path_positions: Vec<bool>,  // true = right, false = left
}

/// Trace segment witness data (per trace commitment)
#[derive(Clone, Debug)]
pub struct TraceSegmentWitness {
    pub queries: Vec<TraceQuery>,        // Values for this segment only
    pub batch_nodes: Vec<Vec<[u8; 32]>>, // Batch Merkle siblings
    pub batch_depth: u8,                 // Merkle tree depth
    pub batch_indexes: Vec<usize>,       // Positions used in batch verification
}

/// Single composition query opening
#[derive(Clone, Debug)]
pub struct CompQuery {
    pub values: Vec<u64>,           // GL field elements (composition row)
    pub merkle_path: Vec<[u8; 32]>, // RPO-256 sibling nodes
    pub path_positions: Vec<bool>,
}

/// FRI layer queries (one per layer)
#[derive(Clone, Debug)]
pub struct FriLayerQueries {
    pub queries: Vec<FriQuery>, // Per-query in this layer
    // Batch multiproof data for the layer
    pub unique_indexes: Vec<usize>, // folded_positions_unique for this layer
    pub unique_values: Vec<(u64, u64)>, // (v_lo, v_hi) per unique index (t=2)
    pub batch_nodes: Vec<Vec<[u8; 32]>>, // nodes vectors
    pub batch_depth: u8,            // tree depth
}

#[derive(Clone, Debug)]
pub struct FriQuery {
    pub values: Vec<u64>, // All values required to fold this query (length = folding_factor)
}

impl ConstraintSynthesizer<InnerFr> for FullStarkVerifierCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<InnerFr>) -> Result<(), SynthesisError> {
        // Allocate commitment bytes as witnesses (used for both statement hash and later verification)
        let trace_root_bytes: Vec<Vec<UInt8<InnerFr>>> = self
            .trace_commitment_le32
            .iter()
            .map(|root| {
                root.iter()
                    .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<_, _>>()?;
        let comp_root_bytes: Vec<UInt8<InnerFr>> = self
            .comp_commitment_le32
            .iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let fri_roots_bytes: Vec<Vec<UInt8<InnerFr>>> = self
            .fri_commitments_le32
            .iter()
            .map(|root| {
                root.iter()
                    .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
                    .collect()
            })
            .collect::<Result<_, _>>()?;
        let ood_commit_bytes: Vec<UInt8<InnerFr>> = self
            .ood_commitment_le32
            .iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;

        // STEP 1: Bind commitments to public statement hash
        bind_statement_hash(
            cs.clone(),
            self.statement_hash,
            &trace_root_bytes,
            &comp_root_bytes,
            &fri_roots_bytes,
            &ood_commit_bytes,
            &self.stark_pub_inputs,
            &self.query_positions,
            &self.air_params,
        )?;

        // STEP 1.5: Verify OOD frame commitment using light RPO
        use super::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
        let rpo_params = RpoParamsGLLight::default();

        // Allocate OOD values - MATCH Winterfell's merge_ood_evaluations order
        // Per Winterfell source: [trace_current, constraint_current, trace_next, constraint_next]
        let ood_trace_current_fp = gl_alloc_u64_vec(cs.clone(), &self.ood_trace_current)?;
        let ood_comp_current_fp = gl_alloc_u64_vec(cs.clone(), &self.ood_comp)?;
        let ood_trace_next_fp = gl_alloc_u64_vec(cs.clone(), &self.ood_trace_next)?;
        let ood_comp_next_fp = gl_alloc_u64_vec(cs.clone(), &self.ood_comp_next)?;

        let ood_trace_current_gl: Vec<GlVar> = ood_trace_current_fp
            .iter()
            .map(|fp| GlVar(fp.clone()))
            .collect();
        let ood_comp_current_gl: Vec<GlVar> = ood_comp_current_fp
            .iter()
            .map(|fp| GlVar(fp.clone()))
            .collect();
        let ood_trace_next_gl: Vec<GlVar> = ood_trace_next_fp
            .iter()
            .map(|fp| GlVar(fp.clone()))
            .collect();
        let ood_comp_next_gl: Vec<GlVar> = ood_comp_next_fp
            .iter()
            .map(|fp| GlVar(fp.clone()))
            .collect();

        let mut ood_elements_gl = Vec::with_capacity(
            ood_trace_current_gl.len()
                + ood_comp_current_gl.len()
                + ood_trace_next_gl.len()
                + ood_comp_next_gl.len(),
        );
        ood_elements_gl.extend(ood_trace_current_gl.iter().cloned());
        ood_elements_gl.extend(ood_comp_current_gl.iter().cloned());
        ood_elements_gl.extend(ood_trace_next_gl.iter().cloned());
        ood_elements_gl.extend(ood_comp_next_gl.iter().cloned());

        // Hash using light RPO (congruence-only, no internal canonicalization)
        let ood_digest_gl = rpo_hash_elements_light(cs.clone(), &ood_elements_gl, &rpo_params)?;

        // BOUNDARY: Canonicalize computed digest to compare with proof bytes
        let ood_digest_bytes = canonicalize_to_bytes(cs.clone(), &ood_digest_gl)?;

        // Compare canonicalized bytes to proof's OOD commitment bytes
        for (computed, expected) in ood_digest_bytes.iter().zip(ood_commit_bytes.iter()) {
            let eq = computed.is_eq(expected)?;
            eq.enforce_equal(&Boolean::constant(true))?;
        }

        // Enforce non-empty queries and alignment with positions. The circuit now requires
        // the committed query list to be exactly `num_queries` long; if Fiat–Shamir draws
        // collide, the prover must re-sample until all draws are distinct and the proof
        // encodes that full set.
        if self.query_positions.is_empty() {
            return Err(SynthesisError::Unsatisfiable);
        }
        let expected_queries = self.query_positions.len();
        if expected_queries != self.air_params.num_queries {
            return Err(SynthesisError::Unsatisfiable);
        }
        // Prepare holders for query values reused across Merkle + DEEP.
        // Rows are filled from Merkle-verified leaves, so start with empty per-query vectors.
        let mut trace_row_vars: Vec<Vec<GlVar>> = vec![Vec::new(); expected_queries];
        let mut comp_row_vars: Vec<Vec<GlVar>> = vec![Vec::new(); expected_queries];
        if self.comp_queries.len() != expected_queries {
            return Err(SynthesisError::Unsatisfiable);
        }
        let lde_domain_size = self.air_params.trace_len * self.air_params.lde_blowup;
        let mut query_pos_uint_vars: Vec<UInt64GLVar> = Vec::with_capacity(expected_queries);
        for &pos in &self.query_positions {
            if pos >= lde_domain_size {
                return Err(SynthesisError::Unsatisfiable);
            }
            let (pos_uint, _) = gl_alloc_u64(cs.clone(), Some(pos as u64))?;
            query_pos_uint_vars.push(pos_uint);
        }
        for idx in 1..expected_queries {
            let gt = query_pos_uint_vars[idx].is_gt(&query_pos_uint_vars[idx - 1])?;
            gt.enforce_equal(&Boolean::constant(true))?;
        }
        // Ensure data shapes are consistent with commitments
        if let Some(first_segment) = self.trace_segments.first() {
            if first_segment.queries.len() != expected_queries {
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        // STEP 2: Verify trace commitment (batch-only)
        if self.trace_segments.len() != trace_root_bytes.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        for (segment, root_bytes) in self.trace_segments.iter().zip(trace_root_bytes.iter()) {
            if segment.batch_nodes.is_empty() {
                return Err(SynthesisError::Unsatisfiable);
            }
            use super::gadgets::merkle_batch::verify_batch_merkle_root_gl;
            use super::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
            let params = RpoParamsGLLight::default();
            let mut leaves: Vec<[GlVar; 4]> = Vec::with_capacity(segment.queries.len());
            if segment.queries.len() != expected_queries {
                return Err(SynthesisError::Unsatisfiable);
            }
            for (row_idx, q) in segment.queries.iter().enumerate() {
                let mut row_gl: Vec<GlVar> = Vec::with_capacity(q.values.len());
                for &v in &q.values {
                    let gl = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(v)))?);
                    row_gl.push(gl.clone());
                    if let Some(row) = trace_row_vars.get_mut(row_idx) {
                        row.push(gl.clone());
                    } else {
                        return Err(SynthesisError::Unsatisfiable);
                    }
                }
                let digest = rpo_hash_elements_light(cs.clone(), &row_gl, &params)?;
                leaves.push([
                    digest[0].clone(),
                    digest[1].clone(),
                    digest[2].clone(),
                    digest[3].clone(),
                ]);
            }
            verify_batch_merkle_root_gl(
                cs.clone(),
                &params,
                leaves,
                &segment.batch_indexes,
                &segment.batch_nodes,
                segment.batch_depth as usize,
                root_bytes,
            )?;
        }

        // Ensure aggregated trace rows match expected widths / OOD frame
        let expected_trace_width = self.ood_trace_current.len();
        if expected_trace_width == 0 && !trace_row_vars.is_empty() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for row in &trace_row_vars {
            if row.len() != expected_trace_width {
                return Err(SynthesisError::Unsatisfiable);
            }
        }
        // STEP 3: Verify composition commitment (batch-only)
        if !self.comp_batch_nodes.is_empty() {
            use super::gadgets::merkle_batch::verify_batch_merkle_root_gl;
            use super::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
            let params = RpoParamsGLLight::default();
            let mut leaves: Vec<[GlVar; 4]> = Vec::with_capacity(self.comp_queries.len());
            for (row_idx, q) in self.comp_queries.iter().enumerate() {
                let mut row_gl: Vec<GlVar> = Vec::with_capacity(q.values.len());
                for &v in &q.values {
                    let gl = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(v)))?);
                    row_gl.push(gl.clone());
                    if let Some(row) = comp_row_vars.get_mut(row_idx) {
                        row.push(gl.clone());
                    } else {
                        return Err(SynthesisError::Unsatisfiable);
                    }
                }
                let digest = rpo_hash_elements_light(cs.clone(), &row_gl, &params)?;
                leaves.push([
                    digest[0].clone(),
                    digest[1].clone(),
                    digest[2].clone(),
                    digest[3].clone(),
                ]);
            }
            verify_batch_merkle_root_gl(
                cs.clone(),
                &params,
                leaves,
                &self.comp_batch_indexes,
                &self.comp_batch_nodes,
                self.comp_batch_depth as usize,
                &comp_root_bytes,
            )?;
        } else {
            // Missing batch metadata; refuse per-path verification
            return Err(SynthesisError::Unsatisfiable);
        }

        // Use authoritative composition width from AirParams; sanity-check if data present
        let comp_width = self.air_params.comp_width;
        if comp_width == 0 {
            return Err(SynthesisError::Unsatisfiable);
        }
        if self.comp_queries[0].values.len() != comp_width {
            return Err(SynthesisError::Unsatisfiable);
        }
        let expected_comp_width = self.ood_comp.len();
        if expected_comp_width == 0 && !comp_row_vars.is_empty() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for row in &comp_row_vars {
            if row.len() != expected_comp_width {
                return Err(SynthesisError::Unsatisfiable);
            }
        }

        if trace_row_vars.len() != comp_row_vars.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        // STEP 4: Derive FS challenges in-circuit
        let (z, constraint_coeffs, deep_coeffs, fri_betas, raw_query_positions) =
            derive_fs_challenges_in_circuit(
                cs.clone(),
                &trace_root_bytes,
                &comp_root_bytes,
                &fri_roots_bytes,
                &self.fs_context_seed_gl,
                &ood_trace_current_fp,
                &ood_trace_next_fp,
                &ood_comp_current_fp,
                &ood_comp_next_fp,
                self.air_params.num_constraint_coeffs,
                &self.air_params,
                comp_width,
                self.pow_nonce,
            )?;

        enforce_query_positions_alignment(
            &query_pos_uint_vars,
            raw_query_positions,
            expected_queries,
            self.air_params.num_queries,
        )?;
 
        verify_ood_equation_in_circuit(
            cs.clone(),
            &ood_trace_current_gl,
            &ood_trace_next_gl,
            &ood_comp_current_gl,
            &z,
            &constraint_coeffs,
            &self.air_params,
        )?;
        

        // STEP 5: Compute DEEP composition polynomial (returns DEEP evaluations for FRI)
        let deep_evaluations = verify_deep_composition(
            cs.clone(),
            &trace_row_vars,
            &comp_row_vars,
            &ood_trace_current_gl,
            &ood_trace_next_gl,
            &ood_comp_current_gl,
            &ood_comp_next_gl,
            &self.query_positions,
            &z,
            &deep_coeffs,
            &self.air_params,
        )?;

        // STEP 6: Use the heavy FRI verifier for correct semantics
        use super::gadgets::fri::{verify_fri_layers_gl, FriConfigGL, FriLayerQueryGL};

        // Create FRI config using parameters from AIR (no recomputation needed!)
        let fri_config = FriConfigGL {
            folding_factor: self.air_params.fri_folding_factor,
            params_rpo: RpoParamsGLLight::default(),
            terminal: self.air_params.fri_terminal.clone(),
            domain_offset: self.air_params.domain_offset,
            g_lde: self.air_params.g_lde, // Already computed from AIR
            lde_domain_size: self.air_params.trace_len * self.air_params.lde_blowup,
        };

        // Convert layers to FriLayerQueryGL format and enforce witness layer count
        let expected_fri_layers = self.air_params.fri_num_layers;
        let mut fri_layer_queries: Vec<FriLayerQueryGL> = Vec::new();

        if expected_fri_layers == 0 {
            // When no folding layers are expected, the witness must not provide any
            if !self.fri_layers.is_empty() || !fri_betas.is_empty() {
                return Err(SynthesisError::Unsatisfiable);
            }
        } else {
            if self.fri_layers.len() != expected_fri_layers {
                return Err(SynthesisError::Unsatisfiable);
            }
            if fri_betas.len() != expected_fri_layers {
                return Err(SynthesisError::Unsatisfiable);
            }
            if fri_roots_bytes.len() < expected_fri_layers {
                return Err(SynthesisError::Unsatisfiable);
            }

            fri_layer_queries.reserve(expected_fri_layers);
            for layer_idx in 0..expected_fri_layers {
                let layer = &self.fri_layers[layer_idx];
                let root_bytes = &fri_roots_bytes[layer_idx];
                let beta = &fri_betas[layer_idx];
                fri_layer_queries.push(FriLayerQueryGL {
                    queries: &layer.queries,
                    root_bytes,
                    beta,
                    unique_indexes: &layer.unique_indexes,
                    unique_values: &layer.unique_values,
                    batch_nodes: &layer.batch_nodes,
                    batch_depth: layer.batch_depth,
                });
            }
        }

        // Pass deep_evaluations as starting values
        // Note: if remainder coeffs are provided, pass them
        let remainder_coeffs_opt = if self.fri_remainder_coeffs.is_empty() {
            None
        } else {
            Some(self.fri_remainder_coeffs.as_slice())
        };

        // Always verify FRI (including terminal) according to expected configuration
        verify_fri_layers_gl(
            cs.clone(),
            &fri_config,
            &self.query_positions,
            deep_evaluations,
            &fri_layer_queries,
            remainder_coeffs_opt,
        )?;

        Ok(())
    }
}

/// Helper: Convert LE bytes to field element
fn bytes_to_field_le(bytes: &[UInt8<InnerFr>]) -> Result<FpVar<InnerFr>, SynthesisError> {
    if bytes.is_empty() {
        return Ok(FpVar::<InnerFr>::constant(InnerFr::from(0u64)));
    }
    let cs = bytes[0].cs();
    let mut acc = FpVar::<InnerFr>::new_constant(cs.clone(), InnerFr::from(0u64))?;
    let mut pow = FpVar::<InnerFr>::new_constant(cs.clone(), InnerFr::from(1u64))?;
    let base = FpVar::<InnerFr>::constant(InnerFr::from(256u64));
    for b in bytes {
        acc = &acc + &(&b.to_fp()? * &pow);
        pow = &pow * &base;
    }
    Ok(acc)
}

/// Commit query positions using Poseidon (binds them to statement)
fn commit_positions_poseidon(
    cs: ConstraintSystemRef<InnerFr>,
    positions: &[usize],
) -> Result<FpVar<InnerFr>, SynthesisError> {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;

    let mut sponge = PoseidonSpongeVar::new(cs.clone(), &POSEIDON377_PARAMS_T3_V1);
    for &pos in positions {
        let b = (pos as u64).to_le_bytes();
        let bytes: Vec<UInt8<InnerFr>> = b
            .iter()
            .map(|bb| UInt8::new_witness(cs.clone(), || Ok(*bb)))
            .collect::<Result<_, _>>()?;
        // Convert to field & absorb
        let fe = bytes_to_field_le(&bytes)?;
        sponge.absorb(&fe)?;
    }
    let out = sponge.squeeze_field_elements(1)?;
    Ok(out[0].clone())
}

/// Enforce GL field equality: lhs == rhs (mod p_GL)
///
/// Operates in GL field, not Fr377!
/// Enforces: lhs - rhs = (q_plus - q_minus) · p_GL
pub fn enforce_gl_eq(lhs: &FpGLVar, rhs: &FpGLVar) -> Result<(), SynthesisError> {
    enforce_gl_eq_with_bound(lhs, rhs, None)
}

/// Enforce GL field equality with optional quotient bound
///
/// If bound_q is Some(n), enforces |q| ≤ n (useful for round operations where q should be ≤1)
pub fn enforce_gl_eq_with_bound(
    lhs: &FpGLVar,
    rhs: &FpGLVar,
    bound_q: Option<u64>,
) -> Result<(), SynthesisError> {
    use super::gl_u64::{quotient_from_fr_difference, P_GL};
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::uint64::UInt64;
    let cs = lhs.cs();

    // Witness the true Euclidean quotient from concrete values (fits in 64 bits)
    let (q_plus_w, q_minus_w) = (|| -> Result<(u64, u64), SynthesisError> {
        let l = lhs.value().unwrap_or_default();
        let r = rhs.value().unwrap_or_default();

        let (qp, qm) = quotient_from_fr_difference(l, r);
        Ok((qp, qm))
    })()?;

    let q_plus = UInt64::new_witness(cs.clone(), || Ok(q_plus_w))?;
    let q_minus = UInt64::new_witness(cs.clone(), || Ok(q_minus_w))?;

    // If bound specified, enforce it
    if let Some(bound) = bound_q {
        let zero = UInt64::constant(0);

        // (q_plus == 0 || q_minus == 0)
        let qp_is_zero = q_plus.is_eq(&zero)?;
        let qm_is_zero = q_minus.is_eq(&zero)?;
        let one_is_zero = &qp_is_zero | &qm_is_zero; // Use bitwise OR operator
        one_is_zero.enforce_equal(&Boolean::constant(true))?;

        // q_plus ≤ bound && q_minus ≤ bound (enforced via bit check)
        // For bound=1, ensure bits 1..64 are all zero
        let qp_bits = q_plus.to_bits_le()?;
        let qm_bits = q_minus.to_bits_le()?;
        let bound_bits = if bound == 0 {
            0
        } else {
            (bound + 1).next_power_of_two().trailing_zeros() as usize
        };
        for bit in qp_bits.iter().skip(bound_bits.max(1)) {
            bit.enforce_equal(&Boolean::constant(false))?;
        }
        for bit in qm_bits.iter().skip(bound_bits.max(1)) {
            bit.enforce_equal(&Boolean::constant(false))?;
        }
    }

    // Convert (q_plus - q_minus) to a field element
    let q_plus_bits = q_plus.to_bits_le()?;
    let q_minus_bits = q_minus.to_bits_le()?;
    let one = FpGLVar::constant(InnerFr::from(1u64));
    let zero = FpGLVar::constant(InnerFr::from(0u64));

    // Build q_plus_fp from first bit to get proper CS attachment
    let mut q_plus_fp = if q_plus_bits.is_empty() {
        FpGLVar::constant(InnerFr::from(0u64))
    } else {
        FpGLVar::conditionally_select(&q_plus_bits[0], &one, &zero)?
    };
    for (i, bit) in q_plus_bits.iter().enumerate().skip(1) {
        let bit_fp = FpGLVar::conditionally_select(bit, &one, &zero)?;
        q_plus_fp += bit_fp * FpGLVar::constant(InnerFr::from(1u64 << i));
    }

    // Build q_minus_fp similarly
    let mut q_minus_fp = if q_minus_bits.is_empty() {
        FpGLVar::constant(InnerFr::from(0u64))
    } else {
        FpGLVar::conditionally_select(&q_minus_bits[0], &one, &zero)?
    };
    for (i, bit) in q_minus_bits.iter().enumerate().skip(1) {
        let bit_fp = FpGLVar::conditionally_select(bit, &one, &zero)?;
        q_minus_fp += bit_fp * FpGLVar::constant(InnerFr::from(1u64 << i));
    }
    let q_signed = q_plus_fp - q_minus_fp;

    let p_gl_const = FpGLVar::constant(InnerFr::from(P_GL));
    (lhs - rhs).enforce_equal(&(q_signed * p_gl_const))?;
    Ok(())
}

// per-path helpers removed (batch-only)

/// Derive Fiat-Shamir challenges in-circuit
///
/// 0. Seed with context elements
/// 1. Reseed with trace commitment(s) → draw constraint composition coeffs
/// 2. Reseed with comp commitment → draw z
/// 3. Reseed with OOD frames → draw DEEP coeffs + rho
/// 4. Reseed with FRI commitments → draw beta for each layer
/// 5. Query positions derived off-circuit (bound via Poseidon commitment)
///
/// Returns: (z, constraint_coeffs, deep_coeffs, fri_betas, raw_query_positions)
fn derive_fs_challenges_in_circuit(
    cs: ConstraintSystemRef<InnerFr>,
    trace_roots: &[Vec<UInt8<InnerFr>>], // Support multiple trace segments
    comp_root: &[UInt8<InnerFr>],
    fri_roots: &[Vec<UInt8<InnerFr>>],
    fs_context_seed_gl: &[u64], // proof.context.to_elements().as_int()
    ood_trace_current: &[FpGLVar],
    ood_trace_next: &[FpGLVar],
    ood_comp: &[FpGLVar],
    ood_comp_next: &[FpGLVar], // Composition at z*g (for LINEAR batching)
    num_constraint_coeffs: usize, // proof.context.num_constraints()
    air_params: &AirParams,
    comp_width: usize,
    pow_nonce: u64,
) -> Result<(FpGLVar, Vec<FpGLVar>, Vec<FpGLVar>, Vec<FpGLVar>, Vec<UInt64GLVar>), SynthesisError> {
    use super::gadgets::gl_range::gl_alloc_u64_vec;
    use super::gadgets::rpo_gl_light::{RandomCoinGL, RpoParamsGLLight};
    use super::gadgets::utils::digest32_to_gl4;

    // 0) Create counter-based RandomCoin with context seed
    let ctx = gl_alloc_u64_vec(cs.clone(), fs_context_seed_gl)?;
    let ctx_gl: Vec<GlVar> = ctx.iter().map(|fp| GlVar(fp.clone())).collect();
    let mut coin = RandomCoinGL::new(cs.clone(), &ctx_gl, RpoParamsGLLight::default())?;

    // 1) Reseed with each trace commitment, then draw constraint composition coefficients
    for tr in trace_roots {
        let tr_elems = digest32_to_gl4(tr)?;
        let tr_gl: Vec<GlVar> = tr_elems.iter().map(|fp| GlVar(fp.clone())).collect();
        coin.reseed(&tr_gl)?;
    }
    // Draw constraint composition coefficients (now returned for constraint evaluation verification)
    let mut constraint_coeffs = Vec::with_capacity(num_constraint_coeffs);
    for _ in 0..num_constraint_coeffs {
        let cc_gl = coin.draw()?;
        constraint_coeffs.push(cc_gl.0); // Extract FpVar from GlVar
    }

    // 2) Reseed with composition commitment → draw z
    let comp_elems = digest32_to_gl4(comp_root)?;
    let comp_gl: Vec<GlVar> = comp_elems.iter().map(|fp| GlVar(fp.clone())).collect();
    coin.reseed(&comp_gl)?;

    let z_gl = coin.draw()?;
    let z = z_gl.0; // Extract FpVar from GlVar

    // 3) Reseed with OOD frames - hash elements first, then reseed with digest
    let mut ood_gl: Vec<GlVar> = Vec::with_capacity(
        ood_trace_current.len() + ood_comp.len() + ood_trace_next.len() + ood_comp_next.len(),
    );
    ood_gl.extend(ood_trace_current.iter().map(|fp| GlVar(fp.clone())));
    ood_gl.extend(ood_comp.iter().map(|fp| GlVar(fp.clone())));
    ood_gl.extend(ood_trace_next.iter().map(|fp| GlVar(fp.clone())));
    ood_gl.extend(ood_comp_next.iter().map(|fp| GlVar(fp.clone())));

    // HASH the OOD elements first
    use super::gadgets::rpo_gl_light::rpo_hash_elements_light;
    let ood_digest = rpo_hash_elements_light(cs.clone(), &ood_gl, &RpoParamsGLLight::default())?;

    // Then reseed with the digest
    coin.reseed(&ood_digest)?;

    // DEEP coeffs: RandomRho only (one coefficient per column)
    let num_deep = air_params.trace_width + comp_width;
    let mut deep_coeffs = Vec::with_capacity(num_deep);
    for _ in 0..num_deep {
        let coeff_gl = coin.draw()?;
        deep_coeffs.push(coeff_gl.0);
    }

    // 4) Reseed with FRI commitments → draw beta only for folding layers
    let num_fri_layers = air_params.fri_num_layers;
    let mut fri_betas = Vec::with_capacity(num_fri_layers);
    for (i, fri_root) in fri_roots.iter().enumerate() {
        let fr = digest32_to_gl4(fri_root)?;
        let fr_gl: Vec<GlVar> = fr.iter().map(|fp| GlVar(fp.clone())).collect();
        coin.reseed(&fr_gl)?;

        // Only draw beta for actual FOLDING layers (not remainder)
        if i < num_fri_layers {
            let beta_gl = coin.draw()?;
            fri_betas.push(beta_gl.0); // Extract FpVar
        }
    }

    // 5) Derive query positions in-circuit (mirrors Winterfell verifier)
    let grinding_factor = air_params.grinding_factor as usize;
    if grinding_factor > 64 {
        return Err(SynthesisError::Unsatisfiable);
    }
    coin.reseed_with_nonce(pow_nonce, grinding_factor)?;
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let domain_bits = lde_domain_size.trailing_zeros() as usize;
    let mut raw_positions = Vec::with_capacity(air_params.num_queries);
    for _ in 0..air_params.num_queries {
        let pos = coin.draw_integer_masked(domain_bits)?;
        raw_positions.push(pos);
    }

    Ok((z, constraint_coeffs, deep_coeffs, fri_betas, raw_positions))
}

/// Compute DEEP composition polynomial
///
/// Computes DEEP polynomial from trace and composition queries using LINEAR batching.
/// The DEEP polynomial is then passed to FRI for low-degree verification.
pub fn verify_deep_composition(
    cs: ConstraintSystemRef<InnerFr>,
    trace_queries: &[Vec<GlVar>],
    comp_queries: &[Vec<GlVar>],
    ood_trace_current: &[GlVar],
    ood_trace_next: &[GlVar],
    ood_comp: &[GlVar],
    ood_comp_next: &[GlVar],
    query_positions: &[usize],
    z: &FpGLVar,
    deep_coeffs: &[FpGLVar],
    air_params: &AirParams,
) -> Result<Vec<FpGLVar>, SynthesisError> {
    // Returns DEEP evaluations per query for FRI!
    let mut deep_evaluations = Vec::with_capacity(trace_queries.len());

    // LDE domain parameters from AirParams - use LIGHT GL vars
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    if !lde_domain_size.is_power_of_two() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let m = (usize::BITS - 1 - lde_domain_size.leading_zeros()) as usize; // m = log2(N)
    let offset_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.domain_offset)));
    let g_lde_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.g_lde)));
    let g_trace_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.g_trace)));
    let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));

    // Convert z to GlVar for light operations
    let z_gl = GlVar(z.clone());

    // Pre-convert deep coefficients to GlVar once (congruence-only, no range checks)
    let gammas_gl: Vec<GlVar> = deep_coeffs
        .iter()
        .map(|c| GlVar(c.clone())) // Fr value used directly as GL-congruent element
        .collect();

    // Precompute powers of g_lde: pow2[k] = g_lde^(2^k) once, reuse for all queries
    let mut pow2_g_lde: Vec<GlVar> = Vec::with_capacity(m);
    if m > 0 {
        pow2_g_lde.push(g_lde_gl.clone());
        for _ in 1..m {
            let last = pow2_g_lde.last().unwrap().clone();
            pow2_g_lde.push(gl_mul_light(cs.clone(), &last, &last)?);
        }
    }

    // Precompute z*g once (shared by every query)
    let zg_gl = gl_mul_light(cs.clone(), &z_gl, &g_trace_gl)?;

    // Hold numerators and denominator products for shared batch inversion
    let mut numerators: Vec<GlVar> = Vec::with_capacity(trace_queries.len());
    let mut denom_products: Vec<GlVar> = Vec::with_capacity(trace_queries.len());

    // For each query:
    for (q_idx, trace_row) in trace_queries.iter().enumerate() {
        let comp_row = comp_queries
            .get(q_idx)
            .ok_or(SynthesisError::Unsatisfiable)?;
        let position = query_positions.get(q_idx).copied().unwrap_or(0);

        // Bit-decompose position (constant bits, no constraints!)
        let mut position_bits = Vec::with_capacity(m);
        let mut pos = position;
        for _ in 0..m {
            position_bits.push(Boolean::constant((pos & 1) == 1));
            pos >>= 1;
        }

        // Compute x = offset * g_lde^position using precomputed pow2 table
        let mut acc = one_gl.clone();
        for (k, bit) in position_bits.iter().enumerate() {
            if k < pow2_g_lde.len() {
                let sel = GlVar(FpGLVar::conditionally_select(
                    bit,
                    &pow2_g_lde[k].0,
                    &one_gl.0,
                )?);
                acc = gl_mul_light(cs.clone(), &acc, &sel)?;
            }
        }
        let x = gl_mul_light(cs.clone(), &offset_gl, &acc)?;

        // Compute denominators ONCE (shared across all columns)
        let den_z_gl = gl_sub_light(cs.clone(), &x, &z_gl)?;
        let den_zg_gl = gl_sub_light(cs.clone(), &x, &zg_gl)?;
        let denom_product = gl_mul_light(cs.clone(), &den_z_gl, &den_zg_gl)?;

        // DEEP composition per Winterfell's exact formula (composer.rs lines 137-159)
        // Formula: result = (t1_num * t2_den + t2_num * t1_den) / (t1_den * t2_den)
        // Where: t1_num = Σ(T(x)-T(z))*gamma, t2_num = Σ(T(x)-T(z*g))*gamma

        let trace_w = trace_row.len();
        let comp_w = comp_row.len();
        if trace_w != ood_trace_current.len()
            || trace_w != ood_trace_next.len()
            || comp_w != ood_comp.len()
            || comp_w != ood_comp_next.len()
        {
            return Err(SynthesisError::Unsatisfiable);
        }
        let mut coeff_idx = 0;

        // Accumulate numerators for z and z*g terms
        let mut t1_num = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        let mut t2_num = GlVar(FpGLVar::constant(InnerFr::from(0u64)));

        // Process trace columns
        for col in 0..trace_w {
            let t_x = trace_row
                .get(col)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;
            let gamma = gammas_gl[coeff_idx].clone();
            coeff_idx += 1;

            let ood_cur = ood_trace_current
                .get(col)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;
            let diff_z = gl_sub_light(cs.clone(), &t_x, &ood_cur)?;
            let weighted_z = gl_mul_light(cs.clone(), &diff_z, &gamma)?;
            t1_num = gl_add_light(cs.clone(), &t1_num, &weighted_z)?;

            let ood_next_val = ood_trace_next
                .get(col)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;
            let diff_zg = gl_sub_light(cs.clone(), &t_x, &ood_next_val)?;
            let weighted_zg = gl_mul_light(cs.clone(), &diff_zg, &gamma)?;
            t2_num = gl_add_light(cs.clone(), &t2_num, &weighted_zg)?;
        }

        // Process composition columns
        // removed unused debug copies

        for k in 0..comp_w {
            let gamma_c = gammas_gl[coeff_idx].clone();
            coeff_idx += 1;

            let c_x = comp_row
                .get(k)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;
            let c_z = ood_comp
                .get(k)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;
            let c_zg = ood_comp_next
                .get(k)
                .cloned()
                .ok_or(SynthesisError::Unsatisfiable)?;

            let diff_z = gl_sub_light(cs.clone(), &c_x, &c_z)?;
            let weighted_z = gl_mul_light(cs.clone(), &diff_z, &gamma_c)?;
            t1_num = gl_add_light(cs.clone(), &t1_num, &weighted_z)?;

            let diff_zg = gl_sub_light(cs.clone(), &c_x, &c_zg)?;
            let weighted_zg = gl_mul_light(cs.clone(), &diff_zg, &gamma_c)?;
            t2_num = gl_add_light(cs.clone(), &t2_num, &weighted_zg)?;
        }

        let cross_term1 = gl_mul_light(cs.clone(), &t1_num, &den_zg_gl)?;
        let cross_term2 = gl_mul_light(cs.clone(), &t2_num, &den_z_gl)?;
        let numerator = gl_add_light(cs.clone(), &cross_term1, &cross_term2)?;
        numerators.push(numerator);
        denom_products.push(denom_product);
    }

    // Batch invert all denominator products to amortize constraint cost
    let denom_invs = gl_batch_inv_light(cs.clone(), &denom_products)?;
    for (numerator, inv) in numerators.into_iter().zip(denom_invs.into_iter()) {
        let deep_sum = gl_mul_light(cs.clone(), &numerator, &inv)?;
        deep_evaluations.push(deep_sum.0);
    }

    Ok(deep_evaluations)
}

fn enforce_query_positions_alignment(
    expected_positions: &[UInt64GLVar],
    raw_positions: Vec<UInt64GLVar>,
    expected_unique_len: usize,
    total_queries: usize,
) -> Result<(), SynthesisError> {
    if total_queries != raw_positions.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    if expected_positions.len() != expected_unique_len {
        return Err(SynthesisError::Unsatisfiable);
    }
    if total_queries == 0 || expected_unique_len == 0 {
        return Err(SynthesisError::Unsatisfiable);
    }
    if expected_unique_len != total_queries {
        return Err(SynthesisError::Unsatisfiable);
    }

    // Every committed position must appear among the Fiat-Shamir draws
    for expected in expected_positions {
        let mut hit = Boolean::constant(false);
        for raw in &raw_positions {
            let eq = expected.is_eq(raw)?;
            hit = &hit | &eq;
        }
        hit.enforce_equal(&Boolean::constant(true))?;
    }

    // Every derived draw must map to one of the committed unique positions
    for raw in &raw_positions {
        let mut hit = Boolean::constant(false);
        for expected in expected_positions {
            let eq = raw.is_eq(expected)?;
            hit = &hit | &eq;
        }
        hit.enforce_equal(&Boolean::constant(true))?;
    }

    Ok(())
}

// ============================================================================
// STATEMENT HASH BINDING
// ============================================================================

/// Bind all commitments and parameters to the public statement hash.
///
/// This function verifies that the prover's witness matches the public statement
/// by hashing all commitments, public inputs, query positions, and AIR parameters.
/// The computed hash must equal the public statement_hash.
///
/// Security properties:
/// - All structural parameters are witness-allocated and hashed in-circuit
/// - This binds the proof to specific AIR parameters via statement_hash
/// - A prover cannot use different params without invalidating the proof
/// Bind all commitments and parameters to the public statement hash.
///
/// Takes pre-allocated UInt8 witness variables for commitment bytes.
fn bind_statement_hash(
    cs: ConstraintSystemRef<InnerFr>,
    statement_hash: InnerFr,
    trace_root_bytes: &[Vec<UInt8<InnerFr>>],
    comp_root_bytes: &[UInt8<InnerFr>],
    fri_roots_bytes: &[Vec<UInt8<InnerFr>>],
    ood_commit_bytes: &[UInt8<InnerFr>],
    stark_pub_inputs: &[u64],
    query_positions: &[usize],
    air_params: &AirParams,
) -> Result<(), SynthesisError> {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;

    let statement_hash_var = FpVar::<InnerFr>::new_input(cs.clone(), || Ok(statement_hash))?;

    // Hash commitments and verify against public input
    let mut hasher = PoseidonSpongeVar::new(cs.clone(), &POSEIDON377_PARAMS_T3_V1);

    // Absorb trace commitment (as field elements)
    for root in trace_root_bytes {
        for chunk in root.chunks(8) {
            let fe = bytes_to_field_le(chunk)?;
            hasher.absorb(&fe)?;
        }
    }
    // Absorb comp commitment
    for chunk in comp_root_bytes.chunks(8) {
        let fe = bytes_to_field_le(chunk)?;
        hasher.absorb(&fe)?;
    }
    // Absorb FRI commitments
    for fri_root in fri_roots_bytes {
        for chunk in fri_root.chunks(8) {
            let fe = bytes_to_field_le(chunk)?;
            hasher.absorb(&fe)?;
        }
    }
    // Absorb OOD commitment (binds OOD frame, prevents free witnesses)
    for chunk in ood_commit_bytes.chunks(8) {
        let fe = bytes_to_field_le(chunk)?;
        hasher.absorb(&fe)?;
    }

    // Absorb STARK public inputs
    for pub_in in stark_pub_inputs {
        hasher.absorb(&FpVar::constant(InnerFr::from(*pub_in)))?;
    }

    // Commit to query positions and absorb (prevents adversarial positions!)
    let pos_commit = commit_positions_poseidon(cs.clone(), query_positions)?;
    hasher.absorb(&pos_commit)?;

    // Absorb AIR params hash
    let params_hash = hash_air_params(cs.clone(), air_params)?;
    hasher.absorb(&params_hash)?;

    let computed_hash = hasher.squeeze_field_elements(1)?;
    computed_hash[0].enforce_equal(&statement_hash_var)?;

    Ok(())
}

/// Hash all AIR parameters into a single field element.
fn hash_air_params(
    cs: ConstraintSystemRef<InnerFr>,
    air_params: &AirParams,
) -> Result<FpVar<InnerFr>, SynthesisError> {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;

    let mut params_hasher = PoseidonSpongeVar::new(cs.clone(), &POSEIDON377_PARAMS_T3_V1);

    // Domain separator for AIR params binding
    params_hasher.absorb(&FpVar::constant(InnerFr::from(0xA1A1u64)))?;

    // Structural params - allocate as witnesses
    let trace_width_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.trace_width as u64))
    })?;
    let comp_width_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.comp_width as u64))
    })?;
    let trace_len_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.trace_len as u64))
    })?;
    let lde_blowup_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.lde_blowup as u64))
    })?;
    let num_queries_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.num_queries as u64))
    })?;
    let fri_folding_factor_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.fri_folding_factor as u64))
    })?;
    let fri_num_layers_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.fri_num_layers as u64))
    })?;
    let lde_generator_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.lde_generator))
    })?;
    let domain_offset_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.domain_offset))
    })?;
    let g_lde_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.g_lde))
    })?;
    let g_trace_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.g_trace))
    })?;
    let num_constraint_coeffs_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.num_constraint_coeffs as u64))
    })?;
    let grinding_factor_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.grinding_factor as u64))
    })?;

    // Enum params as u64 discriminants
    let combiner_kind_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.combiner_kind.to_u64()))
    })?;
    let fri_terminal_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.fri_terminal.to_u64()))
    })?;

    // Aggregator identity version
    let version_var = FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(air_params.aggregator_version))
    })?;

    // Absorb all params
    params_hasher.absorb(&trace_width_var)?;
    params_hasher.absorb(&comp_width_var)?;
    params_hasher.absorb(&trace_len_var)?;
    params_hasher.absorb(&lde_blowup_var)?;
    params_hasher.absorb(&num_queries_var)?;
    params_hasher.absorb(&fri_folding_factor_var)?;
    params_hasher.absorb(&fri_num_layers_var)?;
    params_hasher.absorb(&lde_generator_var)?;
    params_hasher.absorb(&domain_offset_var)?;
    params_hasher.absorb(&g_lde_var)?;
    params_hasher.absorb(&g_trace_var)?;
    params_hasher.absorb(&num_constraint_coeffs_var)?;
    params_hasher.absorb(&grinding_factor_var)?;
    params_hasher.absorb(&combiner_kind_var)?;
    params_hasher.absorb(&fri_terminal_var)?;
    params_hasher.absorb(&version_var)?;

    // Squeeze params hash
    let params_hash = params_hasher.squeeze_field_elements(1)?;
    Ok(params_hash[0].clone())
}
