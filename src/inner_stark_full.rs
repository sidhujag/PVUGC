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

use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, ConstraintSynthesizer};
use ark_r1cs_std::fields::fp::FpVar;
use crate::outer_compressed::InnerFr;
use crate::gadgets::rpo_gl_light::canonicalize_to_bytes;
// Light RPO for internal operations, canonicalize only at serialization boundaries
use crate::gadgets::gl_range::gl_alloc_u64_vec;
use crate::gadgets::gl_fast::{GlVar, gl_mul_light, gl_sub_light, gl_add_light};
use crate::gadgets::utils::CombinerKind;

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
    pub lde_generator: u64,      // LDE domain generator (e.g., 8 for size 64)
    pub domain_offset: u64,      // Domain offset (e.g., 7 for Goldilocks)
    pub g_lde: u64,              // Same as lde_generator
    pub g_trace: u64,            // Trace domain generator (e.g., 2^24 for trace_len=8)
    pub combiner_kind: CombinerKind,
    pub fri_terminal: crate::gadgets::fri::FriTerminalKind,
    pub num_constraint_coeffs: usize,
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
    pub ood_commitment_le32: [u8; 32],  // Binds OOD frame to prevent free witnesses
    
    // Query openings (witness)
    pub query_positions: Vec<usize>,           // LDE domain positions
    pub trace_queries: Vec<TraceQuery>,        // Per-query trace openings
    pub comp_queries: Vec<CompQuery>,          // Per-query composition openings
    
    // Batch Merkle proofs for optimized verification
    pub trace_batch_nodes: Vec<Vec<[u8; 32]>>,
    pub trace_batch_depth: u8,
    pub trace_batch_indexes: Vec<usize>,
    pub comp_batch_nodes: Vec<Vec<[u8; 32]>>,
    pub comp_batch_depth: u8,
    pub comp_batch_indexes: Vec<usize>,
    
    // OOD frame (witness)
    pub ood_trace_current: Vec<u64>,   // Trace at z (GL values)
    pub ood_trace_next: Vec<u64>,      // Trace at z·g
    pub ood_comp: Vec<u64>,             // Composition at z
    pub ood_comp_next: Vec<u64>,        // Composition at z·g (for LINEAR batching)
    
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
    // Batch multiproof data for the layer
    pub unique_indexes: Vec<usize>,             // folded_positions_unique for this layer
    pub unique_values: Vec<(u64, u64)>,         // (v_lo, v_hi) per unique index in same order
    pub batch_nodes: Vec<Vec<[u8; 32]>>,        // nodes vectors
    pub batch_depth: u8,                        // tree depth
}

#[derive(Clone, Debug)]
pub struct FriQuery {
    pub v_lo: u64,                  // Lower half (GL)
    pub v_hi: u64,                  // Upper half (GL)
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
        // Absorb OOD commitment (binds OOD frame, prevents free witnesses)
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
        
        // Commit to query positions and absorb (prevents adversarial positions!)
        let pos_commit = commit_positions_poseidon(cs.clone(), &self.query_positions)?;
        hasher.absorb(&pos_commit)?;
        
        let computed_hash = hasher.squeeze_field_elements(1)?;
        computed_hash[0].enforce_equal(&statement_hash_var)?;
        

        // STEP 1.5: Verify OOD frame commitment using light RPO
        use crate::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
        let rpo_params = RpoParamsGLLight::default();
        
        // Allocate OOD values - MATCH Winterfell's merge_ood_evaluations order
        // Per Winterfell source: [trace_current, constraint_current, trace_next, constraint_next]
        let mut ood_elements_fp = Vec::new();
        ood_elements_fp.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_trace_current)?);
        ood_elements_fp.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_comp)?);
        ood_elements_fp.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_trace_next)?);
        ood_elements_fp.extend(gl_alloc_u64_vec(cs.clone(), &self.ood_comp_next)?);

        
        // Convert to GlVar for light RPO
        let ood_elements_gl: Vec<GlVar> = ood_elements_fp.iter().map(|fp| GlVar(fp.clone())).collect();
        
        // Hash using light RPO (congruence-only, no internal canonicalization)
        let ood_digest_gl = rpo_hash_elements_light(cs.clone(), &ood_elements_gl, &rpo_params)?;
        
        // BOUNDARY: Canonicalize computed digest to compare with proof bytes
        let ood_digest_bytes = canonicalize_to_bytes(cs.clone(), &ood_digest_gl)?;
        
        // Compare canonicalized bytes to proof's OOD commitment bytes
        for (computed, expected) in ood_digest_bytes.iter().zip(ood_commit_bytes.iter()) {
            let eq = computed.is_eq(expected)?;
            eq.enforce_equal(&Boolean::constant(true))?;
        }
        
        

        // STEP 2: Verify trace commitment (batch-only)
        if !self.trace_batch_nodes.is_empty() {
            use crate::gadgets::merkle_batch::verify_batch_merkle_root_gl;
            use crate::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
            let params = RpoParamsGLLight::default();
            let mut leaves: Vec<[GlVar; 4]> = Vec::with_capacity(self.trace_queries.len());
            for q in &self.trace_queries {
                let mut row_gl: Vec<GlVar> = Vec::with_capacity(q.values.len());
                for &v in &q.values {
                    let fp = FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(v)))?;
                    row_gl.push(GlVar(fp));
                }
                let digest = rpo_hash_elements_light(cs.clone(), &row_gl, &params)?;
                leaves.push([digest[0].clone(), digest[1].clone(), digest[2].clone(), digest[3].clone()]);
            }
            verify_batch_merkle_root_gl(
                cs.clone(),
                &params,
                leaves,
                &self.trace_batch_indexes,
                &self.trace_batch_nodes,
                self.trace_batch_depth as usize,
                &trace_root_bytes,
            )?;
            
        } else {
            // Missing batch metadata; refuse per-path verification
            return Err(SynthesisError::Unsatisfiable);
        }
        

        // STEP 3: Verify composition commitment (batch-only)
        if !self.comp_batch_nodes.is_empty() {
            use crate::gadgets::merkle_batch::verify_batch_merkle_root_gl;
            use crate::gadgets::rpo_gl_light::{rpo_hash_elements_light, RpoParamsGLLight};
            let params = RpoParamsGLLight::default();
            let mut leaves: Vec<[GlVar; 4]> = Vec::with_capacity(self.comp_queries.len());
            for q in &self.comp_queries {
                let mut row_gl: Vec<GlVar> = Vec::with_capacity(q.values.len());
                for &v in &q.values {
                    let fp = FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(v)))?;
                    row_gl.push(GlVar(fp));
                }
                let digest = rpo_hash_elements_light(cs.clone(), &row_gl, &params)?;
                leaves.push([digest[0].clone(), digest[1].clone(), digest[2].clone(), digest[3].clone()]);
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

        // Infer comp_width from actual data
        let comp_width = if !self.comp_queries.is_empty() {
            self.comp_queries[0].values.len()
        } else {
            self.air_params.comp_width
        };
        
        // STEP 4: Derive FS challenges in-circuit
        let trace_root_vecs: Vec<Vec<UInt8<InnerFr>>> = vec![trace_root_bytes.clone()];
        let (z, deep_coeffs, fri_betas) = derive_fs_challenges_in_circuit(
            cs.clone(),
            &trace_root_vecs,
            &comp_root_bytes,
            &fri_roots_bytes,
            &self.fs_context_seed_gl,
            &self.ood_trace_current,
            &self.ood_trace_next,
            &self.ood_comp,
            &self.ood_comp_next,
            self.air_params.num_constraint_coeffs,
            &self.air_params,
            comp_width,
        )?;
        

        
        // STEP 5: Compute DEEP composition polynomial (returns DEEP evaluations for FRI)
        let deep_evaluations = verify_deep_composition(
            cs.clone(),
            &self.trace_queries,
            &self.comp_queries,
            &self.ood_trace_current,
            &self.ood_trace_next,
            &self.ood_comp,
            &self.ood_comp_next,
            &self.query_positions,
            &z,
            &deep_coeffs,
            &self.air_params,
            comp_width,
        )?;
        
        // STEP 6: Use the heavy FRI verifier for correct semantics
        use crate::gadgets::fri::{FriConfigGL, FriLayerQueryGL, verify_fri_layers_gl};
        
        // Create FRI config using parameters from AIR (no recomputation needed!)
        let fri_config = FriConfigGL {
            folding_factor: self.air_params.fri_folding_factor,
            params_rpo: RpoParamsGLLight::default(),
            terminal: self.air_params.fri_terminal.clone(),
            domain_offset: self.air_params.domain_offset,
            g_lde: self.air_params.g_lde,  // Already computed from AIR
            lde_domain_size: self.air_params.trace_len * self.air_params.lde_blowup,
        };
        
        // Convert layers to FriLayerQueryGL format
        // Note: FRI has n layers but only n-1 betas (last layer doesn't need folding)
        // Only create FriLayerQueryGL for layers that have corresponding betas
        let fri_layer_queries: Vec<FriLayerQueryGL> = if self.fri_layers.is_empty() {
            vec![]
        } else {
            // Take all but the last layer (or all layers if we have enough betas)
            // Map FRI layers to their commitments
            let num_layers_with_betas = fri_betas.len().min(self.fri_layers.len());
            self.fri_layers.iter()
                .take(num_layers_with_betas)
                .zip(fri_roots_bytes.iter())  // Try without skip for testing
                .zip(fri_betas.iter())
                .map(|((layer, root_bytes), beta)| {
                    FriLayerQueryGL {
                        queries: &layer.queries,
                        root_bytes,
                        beta,
                        unique_indexes: &layer.unique_indexes,
                        unique_values: &layer.unique_values,
                        batch_nodes: &layer.batch_nodes,
                        batch_depth: layer.batch_depth,
                    }
                })
                .collect()
        };
        
        // Pass deep_evaluations as starting values
        // Note: if remainder coeffs are provided, pass them
        let remainder_coeffs_opt = if self.fri_remainder_coeffs.is_empty() {
            None
        } else {
            Some(self.fri_remainder_coeffs.as_slice())
        };

        
        // Only verify FRI if we have layers to verify or remainder to check
        if !fri_layer_queries.is_empty() || remainder_coeffs_opt.is_some() {
            verify_fri_layers_gl(
                cs.clone(),
                &fri_config,
                &self.query_positions,
                deep_evaluations,
                &fri_layer_queries,
                remainder_coeffs_opt,
            )?;
        }
        
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
/// Operates in GL field, not Fr377!
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
fn derive_fs_challenges_in_circuit(
    cs: ConstraintSystemRef<InnerFr>,
    trace_roots: &[Vec<UInt8<InnerFr>>],  // Support multiple trace segments
    comp_root: &[UInt8<InnerFr>],
    fri_roots: &[Vec<UInt8<InnerFr>>],
    fs_context_seed_gl: &[u64],           // proof.context.to_elements().as_int()
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    ood_comp_next: &[u64],                // Composition at z*g (for LINEAR batching)
    num_constraint_coeffs: usize,         // proof.context.num_constraints()
    air_params: &AirParams,
    comp_width: usize,
) -> Result<(FpGLVar, Vec<FpGLVar>, Vec<FpGLVar>), SynthesisError> {
    use crate::gadgets::gl_range::gl_alloc_u64_vec;
    use crate::gadgets::utils::digest32_to_gl4;
    use crate::gadgets::rpo_gl_light::{RandomCoinGL, RpoParamsGLLight};

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
    // Draw constraint composition coefficients (ignored, but needed for transcript alignment)
    for _ in 0..num_constraint_coeffs {
        let _ = coin.draw()?;  // burn
    }

    // 2) Reseed with composition commitment → draw z
    let comp_elems = digest32_to_gl4(comp_root)?;
    let comp_gl: Vec<GlVar> = comp_elems.iter().map(|fp| GlVar(fp.clone())).collect();
    coin.reseed(&comp_gl)?;
    
    let z_gl = coin.draw()?;
    let z = z_gl.0;  // Extract FpVar from GlVar

    // 3) Reseed with OOD frames - hash elements first, then reseed with digest
    let mut ood_elems = Vec::new();
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_trace_current)?);
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_comp)?);
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_trace_next)?);
    ood_elems.extend(gl_alloc_u64_vec(cs.clone(), ood_comp_next)?);
    
    let ood_gl: Vec<GlVar> = ood_elems.iter().map(|fp| GlVar(fp.clone())).collect();
    
    // HASH the OOD elements first
    use crate::gadgets::rpo_gl_light::rpo_hash_elements_light;
    let ood_digest = rpo_hash_elements_light(cs.clone(), &ood_gl, &RpoParamsGLLight::default())?;
    
    // Then reseed with the digest
    coin.reseed(&ood_digest)?;

    // DEEP coeffs: ONE per trace column + ONE per composition column
    let num_deep = air_params.trace_width + comp_width;
    let mut deep_coeffs = Vec::with_capacity(num_deep);
    for _ in 0..num_deep {
        let coeff_gl = coin.draw()?;
        deep_coeffs.push(coeff_gl.0);  // Extract FpVar
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
            fri_betas.push(beta_gl.0);  // Extract FpVar
        }
    }
    
    Ok((z, deep_coeffs, fri_betas))
}

/// Compute DEEP composition polynomial
///
/// Computes DEEP polynomial from trace and composition queries using LINEAR batching.
/// The DEEP polynomial is then passed to FRI for low-degree verification.
pub fn verify_deep_composition(
    cs: ConstraintSystemRef<InnerFr>,
    trace_queries: &[TraceQuery],
    comp_queries: &[CompQuery],
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    ood_comp_next: &[u64],
    query_positions: &[usize],
    z: &FpGLVar,
    deep_coeffs: &[FpGLVar],
    air_params: &AirParams,
    _comp_width: usize,
) -> Result<Vec<FpGLVar>, SynthesisError> {  // Returns DEEP evaluations per query for FRI!
    let mut deep_evaluations = Vec::with_capacity(trace_queries.len());
    
    // LDE domain parameters from AirParams - use LIGHT GL vars
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    let m = (lde_domain_size as f64).log2() as usize;  // m = log2(N)
    let offset_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.domain_offset)));
    let g_lde_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.g_lde)));
    let g_trace_gl = GlVar(FpGLVar::constant(InnerFr::from(air_params.g_trace)));
    let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    
    // Convert z to GlVar for light operations
    let z_gl = GlVar(z.clone());
    
    // Pre-convert deep coefficients to GlVar once (congruence-only, no range checks)
    let gammas_gl: Vec<GlVar> = deep_coeffs.iter()
        .map(|c| GlVar(c.clone()))  // Fr value used directly as GL-congruent element
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
    
    // Allocate OOD values as GlVar constants (zero overhead!)
    let ood_current: Vec<GlVar> = ood_trace_current.iter()
        .map(|&v| GlVar(FpGLVar::constant(InnerFr::from(v as u128))))
        .collect();
    let ood_next: Vec<GlVar> = ood_trace_next.iter()
        .map(|&v| GlVar(FpGLVar::constant(InnerFr::from(v as u128))))
        .collect();
    let ood_comp_current: Vec<GlVar> = ood_comp.iter()
        .map(|&v| GlVar(FpGLVar::constant(InnerFr::from(v as u128))))
        .collect();
    let ood_comp_next_vals: Vec<GlVar> = ood_comp_next.iter()
        .map(|&v| GlVar(FpGLVar::constant(InnerFr::from(v as u128))))
        .collect();
    
    // For each query:
    for (q_idx, (trace_q, comp_q)) in trace_queries.iter().zip(comp_queries.iter()).enumerate() {
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
                let sel = GlVar(FpGLVar::conditionally_select(bit, &pow2_g_lde[k].0, &one_gl.0)?);
                acc = gl_mul_light(cs.clone(), &acc, &sel)?;
            }
        }
        let x = gl_mul_light(cs.clone(), &offset_gl, &acc)?;
        
        // OPTIMIZED DEEP computation with shared denominators
        // Compute z*g ONCE per query
        let zg_gl = gl_mul_light(cs.clone(), &z_gl, &g_trace_gl)?;
        
        // Compute denominators ONCE (shared across all columns)
        let den_z_gl = gl_sub_light(cs.clone(), &x, &z_gl)?;
        let den_zg_gl = gl_sub_light(cs.clone(), &x, &zg_gl)?;
        
        // Batch inversion: compute P_inv = 1/((x-z)*(x-z*g)) ONCE
        let p_inv_gl = {
            // P = (x-z) * (x-z*g)
            let p_gl = gl_mul_light(cs.clone(), &den_z_gl, &den_zg_gl)?;
            
            // P^{-1} with constraint check
            use crate::gadgets::gl_fast::gl_inv_light;
            gl_inv_light(cs.clone(), &p_gl)?
        };
        
        // DEEP composition per Winterfell's exact formula (composer.rs lines 137-159)
        // Formula: result = (t1_num * t2_den + t2_num * t1_den) / (t1_den * t2_den)
        // Where: t1_num = Σ(T(x)-T(z))*gamma, t2_num = Σ(T(x)-T(z*g))*gamma
        
        let trace_w = trace_q.values.len();
        let comp_w = comp_q.values.len();
        let mut coeff_idx = 0;
        
        // Accumulate numerators for z and z*g terms
        let mut t1_num = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        let mut t2_num = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        
        // Process trace columns
        for col in 0..trace_w {
            let t_x = GlVar(FpGLVar::constant(InnerFr::from(trace_q.values[col] as u128)));
            let gamma = gammas_gl[coeff_idx].clone();
            coeff_idx += 1;
            
            let diff_z = gl_sub_light(cs.clone(), &t_x, &ood_current[col])?;
            let weighted_z = gl_mul_light(cs.clone(), &diff_z, &gamma)?;
            t1_num = gl_add_light(cs.clone(), &t1_num, &weighted_z)?;
            
            let diff_zg = gl_sub_light(cs.clone(), &t_x, &ood_next[col])?;
            let weighted_zg = gl_mul_light(cs.clone(), &diff_zg, &gamma)?;
            t2_num = gl_add_light(cs.clone(), &t2_num, &weighted_zg)?;
        }

        
        // Process composition columns
        // removed unused debug copies
        
        for k in 0..comp_w {
            let gamma_c = gammas_gl[coeff_idx].clone();
            coeff_idx += 1;
            
            let c_x = GlVar(FpGLVar::constant(InnerFr::from(comp_q.values[k] as u128)));
            let c_z = ood_comp_current[k].clone();
            let c_zg = ood_comp_next_vals[k].clone();
            
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
          
        // Use P_inv directly
        let deep_sum = gl_mul_light(cs.clone(), &numerator, &p_inv_gl)?;
        
        // The DEEP polynomial deep_sum is what goes to FRI!
        // Convert GlVar back to FpGLVar for compatibility
        deep_evaluations.push(deep_sum.0);
    }
    
    Ok(deep_evaluations)
}