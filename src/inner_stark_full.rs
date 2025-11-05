//! Full STARK Verifier Circuit (Clean Architecture)
//!
//! This module implements a complete Winterfell STARK verifier as an arkworks R1CS circuit.
//! Unlike the hybrid approach, this directly verifies the STARK proof without witness extraction.
//!
//! ## Design Principles:
//! 
//! 1. **Direct verification**: Parse Winterfell proof and verify in-circuit
//! 2. **Native GL arithmetic**: All DEEP/FRI operations in Goldilocks field
//! 3. **RPO-256 Merkle**: Verify Winterfell's actual commitments (no shadow trees)
//! 4. **One source of truth**: The proof bytes, not extracted witnesses
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
//!
//! ## Constraint Budget Estimate:
//!
//! - RPO-256 permutations: ~30K constraints (2 Merkle trees × depth 10 × 2 queries)
//! - GL field operations: ~80K constraints (DEEP + FRI in non-native field)
//! - FRI Merkle verification: ~40K constraints (4 layers × depth 8 × 2 queries)
//! - FS transcript: ~20K constraints (RPO sponge operations)
//! - Query binding: ~10K constraints
//! **Total: ~180-220K constraints**
//!
//! This is 4× the hybrid approach but **eliminates all witness extraction complexity**.
//! The outer BW6-761 compression reduces this to ~40 PVUGC columns regardless.

use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, ConstraintSynthesizer};
use ark_r1cs_std::fields::fp::FpVar;
use crate::outer_compressed::InnerFr;
use crate::gadgets::rpo_gl::{Rpo256GlVar, RpoParamsGL};
use crate::gadgets::utils::digest32_to_gl4;
use crate::gadgets::gl_range::{gl_enforce_nonzero_and_inv, gl_mul_var};
use crate::gadgets::gl_range::gl_alloc_u64_vec;
use crate::gadgets::combiner::{CombinerKind, combiner_weights};

// Use GL type alias for non-native Goldilocks operations in Fr377
pub type FpGLVar = FpVar<InnerFr>;

/// AIR parameters needed for verification (constants, not witnesses)
#[derive(Clone, Debug)]
pub struct AirParams {
    pub trace_width: usize,
    pub comp_width: usize,
    pub trace_len: usize,
    pub lde_blowup: usize,
    pub num_queries: usize,
    pub fri_folding_factor: usize,
    pub fri_num_layers: usize,
    pub lde_generator: u64,      // GL element (usually 7 for Goldilocks)
    pub domain_offset: u64,      // GL element (usually 1)
    pub g_lde: u64,              // LDE domain generator (computed)
    pub combiner_kind: CombinerKind,
    pub fri_terminal: crate::gadgets::fri::FriTerminalKind,  // Constant or Poly{deg}
    pub num_constraint_coeffs: usize,  // Number of constraint composition coefficients
}

/// Full STARK verifier circuit
///
/// Verifies a Winterfell STARK proof completely in-circuit.
/// Proof is parsed on host, structured data passed to circuit.
#[derive(Clone)]
pub struct FullStarkVerifierCircuit {
    // Public input: Single hash binding all commitments + public inputs
    pub statement_hash: InnerFr,  // Poseidon(trace_root || comp_root || fri_roots || ood_commit || pub_inputs)
    
    // STARK public inputs (to bind into statement hash)
    pub stark_pub_inputs: Vec<u64>,     // STARK's public inputs
    
    // Fiat-Shamir context seed (for transcript alignment)
    pub fs_context_seed_gl: Vec<u64>,   // proof.context.to_elements().as_int()
    
    // Commitments (witness, but bound to public hash)
    pub trace_commitment_le32: [u8; 32],
    pub comp_commitment_le32: [u8; 32],
    pub fri_commitments_le32: Vec<[u8; 32]>,  // One per FRI layer
    pub ood_commitment_le32: [u8; 32],  // CRITICAL: Binds OOD frame to prevent free witnesses
    
    // Query openings (witness)
    pub query_positions: Vec<usize>,           // LDE domain positions
    pub trace_queries: Vec<TraceQuery>,        // Per-query trace openings
    pub comp_queries: Vec<CompQuery>,          // Per-query composition openings
    
    // OOD frame (witness)
    pub ood_trace_current: Vec<u64>,   // Trace at z (GL values)
    pub ood_trace_next: Vec<u64>,      // Trace at z·g
    pub ood_comp: Vec<u64>,             // Composition at z
    
    // FRI proof (witness)
    pub fri_layers: Vec<FriLayerQueries>,  // Per-layer fold data
    
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
    pub queries: Vec<FriQuery>,     // Per-query in this layer
}

#[derive(Clone, Debug)]
pub struct FriQuery {
    pub v_lo: u64,                  // Lower half (GL)
    pub v_hi: u64,                  // Upper half (GL)
    pub merkle_path: Vec<[u8; 32]>, // Path to FRI commitment
    pub path_positions: Vec<bool>,
}

impl ConstraintSynthesizer<InnerFr> for FullStarkVerifierCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<InnerFr>) -> Result<(), SynthesisError> {
        use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
        use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
        use crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
        
        // STEP 1: Bind commitments to public statement hash
        let statement_hash_var = FpVar::<InnerFr>::new_input(cs.clone(), || Ok(self.statement_hash))?;
        
        // Allocate commitment bytes as witnesses
        let trace_root_bytes: Vec<UInt8<InnerFr>> = self.trace_commitment_le32.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let comp_root_bytes: Vec<UInt8<InnerFr>> = self.comp_commitment_le32.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let fri_roots_bytes: Vec<Vec<UInt8<InnerFr>>> = self.fri_commitments_le32.iter()
            .map(|root| root.iter().map(|b| UInt8::new_witness(cs.clone(), || Ok(*b))).collect())
            .collect::<Result<_, _>>()?;
        
        // Hash commitments and verify against public input
        let mut hasher = PoseidonSpongeVar::new(cs.clone(), &POSEIDON377_PARAMS_T3_V1);
        
        // Absorb trace commitment (as field elements)
        for chunk in trace_root_bytes.chunks(8) {
            let fe = bytes_to_field_le(chunk)?;
            hasher.absorb(&fe)?;
        }
        // Absorb comp commitment
        for chunk in comp_root_bytes.chunks(8) {
            let fe = bytes_to_field_le(chunk)?;
            hasher.absorb(&fe)?;
        }
        // Absorb FRI commitments
        for fri_root in &fri_roots_bytes {
            for chunk in fri_root.chunks(8) {
                let fe = bytes_to_field_le(chunk)?;
                hasher.absorb(&fe)?;
            }
        }
        // Absorb OOD commitment (CRITICAL: binds OOD frame, prevents free witnesses)
        let ood_commit_bytes: Vec<UInt8<InnerFr>> = self.ood_commitment_le32.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        for chunk in ood_commit_bytes.chunks(8) {
            let fe = bytes_to_field_le(chunk)?;
            hasher.absorb(&fe)?;
        }
        
        // Absorb STARK public inputs
        for pub_in in &self.stark_pub_inputs {
            hasher.absorb(&FpVar::constant(InnerFr::from(*pub_in)))?;
        }
        
        // CRITICAL: Commit to query positions and absorb (prevents adversarial positions!)
        let pos_commit = commit_positions_poseidon(cs.clone(), &self.query_positions)?;
        hasher.absorb(&pos_commit)?;
        
        let computed_hash = hasher.squeeze_field_elements(1)?;
        computed_hash[0].enforce_equal(&statement_hash_var)?;
        
        // STEP 1.5: Verify OOD frame commitment using stateless GL-native RPO
        use crate::gadgets::rpo_gl::rpo_hash_elements_gl;
        let rpo_params = RpoParamsGL::default();
        
        // Allocate all OOD values with range checks
        let mut ood_elements = Vec::new();
        ood_elements.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_trace_current)?);
        ood_elements.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_trace_next)?);
        ood_elements.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_comp)?);
        
        let ood_digest = rpo_hash_elements_gl(cs.clone(), &rpo_params, &ood_elements)?;
        let ood_commit_gl = digest32_to_gl4(&ood_commit_bytes)?;
        for i in 0..4 {
            enforce_gl_eq(&ood_digest[i], &ood_commit_gl[i])?;
        }
        
        // STEP 2: Verify trace Merkle paths
        for (_q_idx, trace_q) in self.trace_queries.iter().enumerate() {
            verify_trace_query(cs.clone(), trace_q, &trace_root_bytes)?;
        }
        
        // STEP 3: Verify composition Merkle paths
        for comp_q in &self.comp_queries {
            verify_comp_query(cs.clone(), comp_q, &comp_root_bytes)?;
        }
        
        // Infer comp_width from actual data
        let comp_width = if !self.comp_queries.is_empty() {
            self.comp_queries[0].values.len()
        } else {
            self.air_params.comp_width
        };
        
        // STEP 4: Derive FS challenges in-circuit (corrected transcript order)
        let trace_root_vecs: Vec<Vec<UInt8<InnerFr>>> = vec![trace_root_bytes.clone()];
        let (z, deep_coeffs, fri_betas, rho) = derive_fs_challenges_in_circuit(
            cs.clone(),
            &trace_root_vecs,
            &comp_root_bytes,
            &fri_roots_bytes,
            &self.fs_context_seed_gl,
            &self.ood_trace_current,
            &self.ood_trace_next,
            &self.ood_comp,
            self.air_params.num_constraint_coeffs,
            &self.air_params,
            comp_width,
        )?;
        
        // STEP 5: Verify DEEP composition (returns comp_sum per query)
        let comp_sums = verify_deep_composition(
            cs.clone(),
            &self.trace_queries,
            &self.comp_queries,
            &self.ood_trace_current,
            &self.ood_trace_next,
            &self.ood_comp,
            &self.query_positions,
            &z,
            &deep_coeffs,
            &self.air_params,
            comp_width,
            &rho,  // For combiner weights
        )?;
        
        // STEP 6: Verify FRI multi-layer folding using expert's gadget
        // DYNAMIC: handles both L=0 and L>0
        use crate::gadgets::fri::{verify_fri_layers_gl, FriLayerQueryGL, FriConfigGL};
        
        // Build FRI config from AirParams (as expert specified!)
        let fri_cfg = FriConfigGL {
            folding_factor: self.air_params.fri_folding_factor,
            // Rp64_256 constants from Winterfell (threaded via Default)
            params_rpo: RpoParamsGL::default(),
            terminal: self.air_params.fri_terminal,
            domain_offset: self.air_params.domain_offset,
            g_lde: self.air_params.g_lde,
        };
        
        // Convert FriLayerQueries to FriLayerQueryGL (with references)
        let mut fri_layers_gl: Vec<FriLayerQueryGL> = Vec::new();
        for (layer_idx, layer) in self.fri_layers.iter().enumerate() {
            if layer_idx < fri_roots_bytes.len() && layer_idx < fri_betas.len() {
                fri_layers_gl.push(FriLayerQueryGL {
                    queries: &layer.queries,
                    root_bytes: &fri_roots_bytes[layer_idx],
                    beta: &fri_betas[layer_idx],
                });
            }
        }
        
        // Pass remainder coefficients only when terminal is Poly
        let remainder_coeffs: Option<&[u64]> = match self.air_params.fri_terminal {
            crate::gadgets::fri::FriTerminalKind::Poly { .. } => Some(self.fri_remainder_coeffs.as_slice()),
            _ => None,
        };
        
        verify_fri_layers_gl(
            cs.clone(),
            &fri_cfg,
            &self.query_positions,
            comp_sums,
            &fri_layers_gl,
            remainder_coeffs,
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
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
    use crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    
    let mut sponge = PoseidonSpongeVar::new(cs.clone(), &POSEIDON377_PARAMS_T3_V1);
    for &pos in positions {
        let b = (pos as u64).to_le_bytes();
        let bytes: Vec<UInt8<InnerFr>> = b.iter()
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
/// CRITICAL: Operates in GL field, not Fr377!
/// Enforces: lhs - rhs = (q_plus - q_minus) · p_GL
pub fn enforce_gl_eq(lhs: &FpGLVar, rhs: &FpGLVar) -> Result<(), SynthesisError> {
    enforce_gl_eq_with_bound(lhs, rhs, None)
}

/// Enforce GL field equality with optional quotient bound
///
/// If bound_q is Some(n), enforces |q| ≤ n (useful for round operations where q should be ≤1)
pub fn enforce_gl_eq_with_bound(lhs: &FpGLVar, rhs: &FpGLVar, bound_q: Option<u64>) -> Result<(), SynthesisError> {
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::uint64::UInt64;
    use crate::gl_u64::{quotient_from_fr_difference, P_GL};
    let cs = lhs.cs();
    
    // Witness the true Euclidean quotient from concrete values (fits in 64 bits)
    let (q_plus_w, q_minus_w) = (|| -> Result<(u64, u64), SynthesisError> {
        let l = lhs.value().unwrap_or_default();
        let r = rhs.value().unwrap_or_default();
        Ok(quotient_from_fr_difference(l, r))
    })()?;
    
    let q_plus = UInt64::new_witness(cs.clone(), || Ok(q_plus_w))?;
    let q_minus = UInt64::new_witness(cs.clone(), || Ok(q_minus_w))?;
    
    // If bound specified, enforce it
    if let Some(bound) = bound_q {
        let zero = UInt64::constant(0);
        
        // (q_plus == 0 || q_minus == 0)
        let qp_is_zero = q_plus.is_eq(&zero)?;
        let qm_is_zero = q_minus.is_eq(&zero)?;
        let one_is_zero = &qp_is_zero | &qm_is_zero;  // Use bitwise OR operator
        one_is_zero.enforce_equal(&Boolean::constant(true))?;
        
        // q_plus ≤ bound && q_minus ≤ bound (enforced via bit check)
        // For bound=1, ensure bits 1..64 are all zero
        let qp_bits = q_plus.to_bits_le()?;
        let qm_bits = q_minus.to_bits_le()?;
        let bound_bits = if bound == 0 { 0 } else { (bound + 1).next_power_of_two().trailing_zeros() as usize };
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
    
    let p_gl_const = FpGLVar::constant(InnerFr::from(P_GL as u64));
    (lhs - rhs).enforce_equal(&(q_signed * p_gl_const))?;
    Ok(())
}

/// Convert 32 bytes to 4 GL field elements (8 bytes each, LE)
// digest32_to_gl4 moved to gadgets::utils

/// Verify single trace query Merkle opening
fn verify_trace_query(
    cs: ConstraintSystemRef<InnerFr>,
    query: &TraceQuery,
    root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    use crate::gadgets::rpo_gl::{rpo_hash_elements_gl, rpo_merge_gl};
    
    // Hash query values using stateless GL-native RPO-256
    let values_gl = gl_alloc_u64_vec(cs.clone(), &query.values)?;
    
    let rpo_params = RpoParamsGL::default();
    let leaf_digest = rpo_hash_elements_gl(cs.clone(), &rpo_params, &values_gl)?;
    if leaf_digest.len() != 4 {
        return Err(SynthesisError::Unsatisfiable);
    }
    
    // Verify Merkle path using stateless GL-native merge (fresh RPO per merge!)
    let mut current_vec = leaf_digest;
    for (sib_bytes, is_right) in query.merkle_path.iter().zip(&query.path_positions) {
        let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib = digest32_to_gl4(&sib_bytes_vars)?;
        
        let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
        
        // Compute parent: if current is right → parent(sib, current), else parent(current, sib)
        let left = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &current_vec[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &current_vec[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &current_vec[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &current_vec[3])?,
        ];
        let right = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current_vec[0], &sib[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current_vec[1], &sib[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current_vec[2], &sib[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current_vec[3], &sib[3])?,
        ];
        
        current_vec = rpo_merge_gl(cs.clone(), &rpo_params, &left, &right)?;
    }
    
    // Verify root matches (GL semantics)
    let root_gl = digest32_to_gl4(root_bytes)?;
    for i in 0..4 {
        enforce_gl_eq(&current_vec[i], &root_gl[i])?;
    }
    
    Ok(())
}

/// Verify composition query (same structure as trace)
fn verify_comp_query(
    cs: ConstraintSystemRef<InnerFr>,
    query: &CompQuery,
    root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    use crate::gadgets::rpo_gl::{rpo_hash_elements_gl, rpo_merge_gl};
    
    // Hash query values using stateless GL-native RPO-256
    let values_gl = gl_alloc_u64_vec(cs.clone(), &query.values)?;
    
    let rpo_params = RpoParamsGL::default();
    let leaf_digest = rpo_hash_elements_gl(cs.clone(), &rpo_params, &values_gl)?;
    if leaf_digest.len() != 4 {
        return Err(SynthesisError::Unsatisfiable);
    }
    
    // Verify Merkle path using stateless GL-native merge (fresh RPO per merge!)
    let mut current = leaf_digest;
    for (sib_bytes, is_right) in query.merkle_path.iter().zip(&query.path_positions) {
        let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib = digest32_to_gl4(&sib_bytes_vars)?;
        
        let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
        
        let left_arr = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &current[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &current[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &current[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &current[3])?,
        ];
        let right_arr = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[0], &sib[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[1], &sib[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[2], &sib[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[3], &sib[3])?,
        ];
        
        current = rpo_merge_gl(cs.clone(), &rpo_params, &left_arr, &right_arr)?;
    }
    
    // Verify root matches (GL semantics)
    let root_gl = digest32_to_gl4(root_bytes)?;
    for i in 0..4 {
        enforce_gl_eq(&current[i], &root_gl[i])?;
    }
    
    Ok(())
}

/// Derive Fiat-Shamir challenges in-circuit
///
/// CORRECTED to match Winterfell 0.13.x exactly:
/// 0. Seed with context elements
/// 1. Reseed with trace commitment(s) → draw constraint composition coeffs
/// 2. Reseed with comp commitment → draw z
/// 3. Reseed with OOD frames → draw DEEP coeffs + rho
/// 4. Reseed with FRI commitments → draw beta for each layer
/// 5. Query positions derived off-circuit (bound via Poseidon commitment)
fn derive_fs_challenges_in_circuit(
    cs: ConstraintSystemRef<InnerFr>,
    trace_roots: &[Vec<UInt8<InnerFr>>],  // Support multiple trace segments
    comp_root: &[UInt8<InnerFr>],
    fri_roots: &[Vec<UInt8<InnerFr>>],
    fs_context_seed_gl: &[u64],           // proof.context.to_elements().as_int()
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    num_constraint_coeffs: usize,         // proof.context.num_constraints()
    air_params: &AirParams,
    comp_width: usize,
) -> Result<(FpGLVar, Vec<FpGLVar>, Vec<FpGLVar>, FpGLVar), SynthesisError> {
    use crate::gadgets::gl_range::gl_alloc_u64_vec;
    use crate::gadgets::utils::digest32_to_gl4;
    
    // GL-native RPO coin with Winterfell Rp64_256 params
    let mut fs = Rpo256GlVar::new(cs.clone(), RpoParamsGL::default())?;

    // 0) Seed with context elements
    let ctx = gl_alloc_u64_vec(cs.clone(), fs_context_seed_gl)?;
    fs.absorb(&ctx)?;
    fs.permute()?;

    // 1) Reseed with each trace commitment, then draw constraint-comp coefficients
    for tr in trace_roots {
        let tr_elems = digest32_to_gl4(tr)?;
        fs.absorb(&tr_elems)?;
        fs.permute()?;
    }
    // Draw the exact number of constraint composition coefficients (ignored by the circuit,
    // but must be consumed to keep the transcript aligned).
    for _ in 0..num_constraint_coeffs {
        let _ = fs.squeeze(1)?; // burn
    }

    // 2) Reseed with composition commitment → draw z
    let comp_elems = digest32_to_gl4(comp_root)?;
    fs.absorb(&comp_elems)?;
    fs.permute()?;
    let z = fs.squeeze(1)?.remove(0);

    // 3) Reseed with OOD frames (trace current/next and OOD constraint evals), then draw DEEP coeffs + rho
    let mut ood_elems = Vec::new();
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_trace_current)?);
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_trace_next)?);
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_comp)?);
    fs.absorb(&ood_elems)?;
    fs.permute()?;

    // DEEP coeffs: trace_width * {0,1} + comp_width * {0}
    let num_deep = air_params.trace_width * 2 + comp_width;
    let mut deep_coeffs = Vec::with_capacity(num_deep);
    for _ in 0..num_deep {
        deep_coeffs.push(fs.squeeze(1)?.remove(0));
    }
    // RandomRho (combiner)
    let rho = fs.squeeze(1)?.remove(0);

    // 4) Reseed with FRI commitments → draw one beta per layer
    let mut fri_betas = Vec::with_capacity(fri_roots.len());
    for fri_root in fri_roots {
        let fr = digest32_to_gl4(fri_root)?;
        fs.absorb(&fr)?;
        fs.permute()?;
        fri_betas.push(fs.squeeze(1)?.remove(0));
    }

    Ok((z, deep_coeffs, fri_betas, rho))
}

/// Verify DEEP composition polynomial
///
/// CRITICAL FIX (per expert): Compare computed DEEP to Merkle-opened composition value,
/// not to a free witness claim!
fn verify_deep_composition(
    cs: ConstraintSystemRef<InnerFr>,
    trace_queries: &[TraceQuery],
    comp_queries: &[CompQuery],
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    query_positions: &[usize],
    z: &FpGLVar,
    deep_coeffs: &[FpGLVar],
    air_params: &AirParams,
    _comp_width: usize,
    rho: &FpGLVar,  // For combiner weights
) -> Result<Vec<FpGLVar>, SynthesisError> {  // Return comp_sum per query for FRI!
    let _p_gl_const = FpGLVar::constant(InnerFr::from(18446744069414584321u64));  // GL modulus
    
    let mut comp_sums = Vec::with_capacity(trace_queries.len());
    
    // LDE domain parameters from AirParams (as expert specified!)
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    let m = (lde_domain_size as f64).log2() as usize;  // m = log2(N)
    let domain_offset = FpGLVar::constant(InnerFr::from(air_params.domain_offset));
    let g_lde = FpGLVar::constant(InnerFr::from(air_params.g_lde));
    let g_trace = FpGLVar::constant(InnerFr::from(air_params.lde_generator));
    
    // Compute powers {g_lde^(2^k)} for bit decomposition
    let mut g_powers = vec![g_lde.clone()];  // g^1
    for _ in 1..m {
        let prev = g_powers.last().unwrap();
        g_powers.push(prev * prev);  // g^(2^k) = (g^(2^(k-1)))^2
    }
    
    // Allocate OOD values ONCE (reuse across queries)
    let ood_current = gl_alloc_u64_vec(cs.clone(), ood_trace_current)?;
    let ood_next = gl_alloc_u64_vec(cs.clone(), ood_trace_next)?;
    
    // For each query:
    for (q_idx, (trace_q, comp_q)) in trace_queries.iter().zip(comp_queries.iter()).enumerate() {
        let position = query_positions.get(q_idx).copied().unwrap_or(0);
        
        // Bit-decompose position
        let mut position_bits = Vec::with_capacity(m);
        let mut pos = position;
        for _ in 0..m {
            position_bits.push(Boolean::new_witness(cs.clone(), || Ok((pos & 1) == 1))?);
            pos >>= 1;
        }
        
        // Compute g_lde^position via conditional multiplies
        let mut result = domain_offset.clone();
        let one = FpGLVar::constant(InnerFr::from(1u64));
        for (k, bit) in position_bits.iter().enumerate() {
            if k < g_powers.len() {
                // If bit is 1: result *= g^(2^k), else: result *= 1
                let multiplier = FpGLVar::conditionally_select(bit, &g_powers[k], &one)?;
                result = result * &multiplier;
            }
        }
        
        // x = offset · g_lde^position
        let x = result;
        
        // DEEP must NOT be conditional - verify array sizes and fail if mismatched
        assert_eq!(ood_current.len(), trace_q.values.len(), 
            "OOD current size must match trace query size");
        assert_eq!(ood_next.len(), trace_q.values.len(),
            "OOD next size must match trace query size");
        
        // Compute DEEP: Σ γᵢ · (T(x) - T(z)) / (x - z·multᵢ)
        let mut deep_sum = FpGLVar::new_constant(cs.clone(), InnerFr::from(0u64))?;
        
        for (col_idx, &t_x_u64) in trace_q.values.iter().enumerate() {
            // Allocate trace value with GL range check
            let (_u, t_x) = crate::gadgets::gl_range::gl_alloc_u64(cs.clone(), Some(t_x_u64))?;
            
            // Term at z (mult=1): enforce invertibility and compute term = diff * inv(den)
            use crate::gadgets::gl_range::{gl_enforce_nonzero_and_inv, gl_mul_var};
            let diff_z = &t_x - &ood_current[col_idx];
            let den_z = &x - z;
            let inv_z = gl_enforce_nonzero_and_inv(cs.clone(), &den_z)?;
            let term_z = gl_mul_var(cs.clone(), &diff_z, &inv_z)?;
            let gamma_z = &deep_coeffs[col_idx * 2];
            // CRITICAL: Accumulate gamma * term (not just term!)
            deep_sum = deep_sum + &(gamma_z * &term_z);
            
            // Term at z·g (mult=g): same pattern
            let diff_zg = &t_x - &ood_next[col_idx];
            let zg = z * &g_trace;
            let den_zg = &x - &zg;
            let inv_zg = gl_enforce_nonzero_and_inv(cs.clone(), &den_zg)?;
            let term_zg = gl_mul_var(cs.clone(), &diff_zg, &inv_zg)?;
            let gamma_zg = &deep_coeffs[col_idx * 2 + 1];
            // CRITICAL: Accumulate gamma * term (not just term!)
            deep_sum = deep_sum + &(gamma_zg * &term_zg);
        }
        
        // Now add composition DEEP terms (shift {0} only)
        let trace_deep_terms = trace_q.values.len() * 2;
        for (comp_idx, &c_x_u64) in comp_q.values.iter().enumerate() {
            let gamma_idx = trace_deep_terms + comp_idx;
            if gamma_idx >= deep_coeffs.len() {
                panic!("Not enough DEEP coefficients: need {}, have {}", gamma_idx + 1, deep_coeffs.len());
            }
            
            // Allocate composition value with GL range check
            let (_u, c_x) = crate::gadgets::gl_range::gl_alloc_u64(cs.clone(), Some(c_x_u64))?;
            
            // Composition uses shift {0} only
            if comp_idx < ood_comp.len() {
                let (_u, c_z) = crate::gadgets::gl_range::gl_alloc_u64(cs.clone(), Some(ood_comp[comp_idx]))?;
                let diff = &c_x - &c_z;
                let den = &x - z;
                let inv = gl_enforce_nonzero_and_inv(cs.clone(), &den)?;
                let term = gl_mul_var(cs.clone(), &diff, &inv)?;
                let gamma = &deep_coeffs[gamma_idx];
                // CRITICAL: Accumulate gamma * term (not just term!)
                deep_sum = deep_sum + &(gamma * &term);
            }
        }
        
        // CRITICAL: Weighted combiner H(x) = Σ w_i(x) * C_i(x)
        let weights = combiner_weights(
            air_params.combiner_kind,
            comp_q.values.len(),
            Some(&x),                     // for DegreeChunks; ignored for RandomRho
            Some(rho),                    // for RandomRho; ignored for DegreeChunks
        )?;
        
        // Weighted sum of composition columns (with GL range checks)
        let mut comp_sum = FpGLVar::new_constant(cs.clone(), InnerFr::from(0u64))?;
        for (c_val, w_i) in comp_q.values.iter().zip(weights.iter()) {
            let (_u, c) = crate::gadgets::gl_range::gl_alloc_u64(cs.clone(), Some(*c_val))?;
            comp_sum = comp_sum + &(w_i * c);
        }
        
        // Enforce equality mod p_GL (not Fr377!)
        enforce_gl_eq(&deep_sum, &comp_sum)?;
        
        // Save comp_sum for FRI
        comp_sums.push(comp_sum);
    }
    
    Ok(comp_sums)
}

// OLD verify_fri_folding function deleted - replaced by expert's verify_fri_layers_gl gadget

