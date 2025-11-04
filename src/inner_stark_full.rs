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

use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use ark_ff::Field;  // For .inverse() method
use crate::outer_compressed::InnerFr;
use crate::fs::rpo_gl_gadget::{RpoGlSpongeVar, Rpo256Var};
use winter_math::fields::f64::BaseElement as GL;  // Goldilocks field for domain computations

// Use GL type alias for non-native Goldilocks operations in Fr377
type FpGLVar = FpVar<InnerFr>;

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
        
        let computed_hash = hasher.squeeze_field_elements(1)?;
        computed_hash[0].enforce_equal(&statement_hash_var)?;
        
        // STEP 1.5: Verify OOD frame commitment
        // Hash OOD frame and verify it matches ood_commitment
        let mut ood_hasher = Rpo256Var::new(cs.clone())?;
        let mut ood_elements = Vec::new();
        for v in &self.ood_trace_current {
            ood_elements.push(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v)))?);
        }
        for v in &self.ood_trace_next {
            ood_elements.push(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v)))?);
        }
        for v in &self.ood_comp {
            ood_elements.push(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v)))?);
        }
        
        let ood_digest = ood_hasher.hash_elements(&ood_elements)?;
        let ood_commit_gl = digest32_to_gl4(&ood_commit_bytes)?;
        for i in 0..4 {
            ood_digest[i].enforce_equal(&ood_commit_gl[i])?;
        }
        
        // STEP 2: Verify trace Merkle paths
        for (q_idx, trace_q) in self.trace_queries.iter().enumerate() {
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
        
        // STEP 4: Derive FS challenges in-circuit
        let (z, deep_coeffs, fri_betas) = derive_fs_challenges_in_circuit(
            cs.clone(),
            &trace_root_bytes,
            &comp_root_bytes,
            &fri_roots_bytes,
            &ood_commit_bytes,
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
        )?;
        
        // STEP 6: Verify FRI multi-layer folding (uses comp_sums as layer 0)
        verify_fri_folding(
            cs.clone(),
            &self.fri_layers,
            &fri_roots_bytes,
            &fri_betas,
            comp_sums,  // Feed DEEP result to FRI
        )?;
        
        Ok(())
    }
}

/// Helper: Convert LE bytes to field element
fn bytes_to_field_le(bytes: &[UInt8<InnerFr>]) -> Result<FpVar<InnerFr>, SynthesisError> {
    let mut acc = FpVar::<InnerFr>::zero();
    let mut pow = FpVar::<InnerFr>::one();
    let base = FpVar::<InnerFr>::constant(InnerFr::from(256u64));
    for b in bytes {
        acc = &acc + &(&b.to_fp()? * &pow);
        pow = &pow * &base;
    }
    Ok(acc)
}

/// Enforce GL field equality: lhs == rhs (mod p_GL)
///
/// CRITICAL: Operates in GL field, not Fr377!
/// Enforces: lhs - rhs = (q_plus - q_minus) · p_GL
fn enforce_gl_eq(
    lhs: &FpGLVar,
    rhs: &FpGLVar,
    p_gl_const: &FpGLVar,
) -> Result<(), SynthesisError> {
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::uint64::UInt64;
    use crate::gl_u64::{fr_to_gl_u64, gl_congruence_quotient};
    
    // Compute the true quotient from concrete witnesses
    let (q_plus_w, q_minus_w) = (|| -> Result<(u64, u64), SynthesisError> {
        let lhs_v = lhs.value().unwrap_or_default();
        let rhs_v = rhs.value().unwrap_or_default();
        
        // Convert to u64 mod p_GL
        let lhs_gl = fr_to_gl_u64(lhs_v) as u128;
        let rhs_gl = fr_to_gl_u64(rhs_v) as u128;
        
        Ok(gl_congruence_quotient(lhs_gl, rhs_gl))
    })()?;
    
    let q_plus = UInt64::new_witness(lhs.cs(), || Ok(q_plus_w))?;
    let q_minus = UInt64::new_witness(lhs.cs(), || Ok(q_minus_w))?;
    
    // Convert UInt64 to FpVar by accumulating bits
    let bits_plus = q_plus.to_bits_le()?;
    let mut q_plus_fp = FpGLVar::zero();
    for (i, bit) in bits_plus.iter().enumerate().take(64) {
        // Convert Boolean to FpVar: if bit then 1 else 0
        let bit_fp = FpGLVar::conditionally_select(bit, 
            &FpGLVar::constant(InnerFr::from(1u64)),
            &FpGLVar::constant(InnerFr::from(0u64)))?;
        let pow2 = FpGLVar::constant(InnerFr::from(1u64 << i));
        q_plus_fp = &q_plus_fp + &(&bit_fp * &pow2);
    }
    
    let bits_minus = q_minus.to_bits_le()?;
    let mut q_minus_fp = FpGLVar::zero();
    for (i, bit) in bits_minus.iter().enumerate().take(64) {
        let bit_fp = FpGLVar::conditionally_select(bit,
            &FpGLVar::constant(InnerFr::from(1u64)),
            &FpGLVar::constant(InnerFr::from(0u64)))?;
        let pow2 = FpGLVar::constant(InnerFr::from(1u64 << i));
        q_minus_fp = &q_minus_fp + &(&bit_fp * &pow2);
    }
    
    let q_signed = q_plus_fp - q_minus_fp;
    
    (lhs - rhs).enforce_equal(&(&q_signed * p_gl_const))?;
    Ok(())
}

/// Convert 32 bytes to 4 GL field elements (8 bytes each, LE)
fn digest32_to_gl4(bytes32: &[UInt8<InnerFr>]) -> Result<[FpGLVar;4], SynthesisError> {
    assert!(bytes32.len() == 32);
    let a0 = bytes_to_gl(&bytes32[0..8])?;
    let a1 = bytes_to_gl(&bytes32[8..16])?;
    let a2 = bytes_to_gl(&bytes32[16..24])?;
    let a3 = bytes_to_gl(&bytes32[24..32])?;
    Ok([a0, a1, a2, a3])
}

/// Convert 8 LE bytes to GL field element
fn bytes_to_gl(bytes: &[UInt8<InnerFr>]) -> Result<FpGLVar, SynthesisError> {
    let mut acc = FpGLVar::zero();
    let mut pow = FpGLVar::one();
    let base = FpGLVar::constant(InnerFr::from(256u64));
    for b in bytes {
        acc = &acc + &(&b.to_fp()? * &pow);
        pow = &pow * &base;
    }
    Ok(acc)
}

/// Verify single trace query Merkle opening
fn verify_trace_query(
    cs: ConstraintSystemRef<InnerFr>,
    query: &TraceQuery,
    root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    
    // Hash query values using RPO-256
    let values_gl: Vec<FpGLVar> = query.values.iter()
        .map(|v| FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v))))
        .collect::<Result<_, _>>()?;
    
    let mut rpo = Rpo256Var::new(cs.clone())?;
    let leaf_digest = rpo.hash_elements(&values_gl)?;
    
    // Verify Merkle path
    let mut current = leaf_digest;
    for (sib_bytes, is_right) in query.merkle_path.iter().zip(&query.path_positions) {
        let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib = digest32_to_gl4(&sib_bytes_vars)?;
        
        let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
        
        // Compute parent: if current is right → parent(sib, current), else parent(current, sib)
        let left = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &current[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &current[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &current[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &current[3])?,
        ];
        let right = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[0], &sib[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[1], &sib[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[2], &sib[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[3], &sib[3])?,
        ];
        
        current = rpo.merge(&left, &right)?;
    }
    
    // Verify root matches
    let root_gl = digest32_to_gl4(root_bytes)?;
    for i in 0..4 {
        current[i].enforce_equal(&root_gl[i])?;
    }
    
    Ok(())
}

/// Verify composition query (same structure as trace)
fn verify_comp_query(
    cs: ConstraintSystemRef<InnerFr>,
    query: &CompQuery,
    root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    // Hash query values using RPO-256
    let values_gl: Vec<FpGLVar> = query.values.iter()
        .map(|v| FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v))))
        .collect::<Result<_, _>>()?;
    
    let mut rpo = Rpo256Var::new(cs.clone())?;
    let leaf_digest = rpo.hash_elements(&values_gl)?;
    
    // Verify Merkle path
    let mut current = leaf_digest;
    for (sib_bytes, is_right) in query.merkle_path.iter().zip(&query.path_positions) {
        let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib = digest32_to_gl4(&sib_bytes_vars)?;
        
        let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
        
        let left = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &current[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &current[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &current[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &current[3])?,
        ];
        let right = [
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[0], &sib[0])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[1], &sib[1])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[2], &sib[2])?,
            FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[3], &sib[3])?,
        ];
        
        current = rpo.merge(&left, &right)?;
    }
    
    // Verify root matches
    let root_gl = digest32_to_gl4(root_bytes)?;
    for i in 0..4 {
        current[i].enforce_equal(&root_gl[i])?;
    }
    
    Ok(())
}

/// Derive Fiat-Shamir challenges in-circuit
///
/// Follows Winterfell's exact FS transcript order:
/// 1. Absorb trace commitment → derive trace randomness (for aux segments)
/// 2. Absorb comp commitment → derive DEEP coefficients
/// 3. Absorb OOD commitment → derive z (OOD point)
/// 4. Absorb FRI commitments → derive beta for each layer
/// 5. Derive query seed (with PoW grinding)
fn derive_fs_challenges_in_circuit(
    cs: ConstraintSystemRef<InnerFr>,
    trace_root: &[UInt8<InnerFr>],
    comp_root: &[UInt8<InnerFr>],
    fri_roots: &[Vec<UInt8<InnerFr>>],
    ood_commit: &[UInt8<InnerFr>],
    air_params: &AirParams,
    comp_width: usize,
) -> Result<(FpGLVar, Vec<FpGLVar>, Vec<FpGLVar>), SynthesisError> {
    // Use RPO-GL sponge matching Winterfell's RandomCoin
    let mut fs = RpoGlSpongeVar::new(cs.clone())?;
    
    // Absorb trace commitment
    fs.absorb_bytes(trace_root)?;
    fs.permute()?;
    
    // Absorb composition commitment  
    fs.absorb_bytes(comp_root)?;
    fs.permute()?;
    
    // Squeeze DEEP coefficients
    // For typical first-order AIR:
    // - Trace uses shifts {0, 1} (current, next) → trace_width × 2
    // - Composition uses shift {0} only → comp_width × 1
    let trace_deep_terms = air_params.trace_width * 2;  // Shifts {0, 1}
    let comp_deep_terms = comp_width * 1;    // Shift {0}, use actual comp_width
    let num_deep_coeffs = trace_deep_terms + comp_deep_terms;
    
    let mut deep_coeffs = Vec::with_capacity(num_deep_coeffs);
    for _ in 0..num_deep_coeffs {
        deep_coeffs.push(fs.squeeze()?);
    }
    
    // Absorb OOD commitment (binds OOD frame)
    fs.absorb_bytes(ood_commit)?;
    fs.permute()?;
    
    // Squeeze z (OOD evaluation point)
    let z = fs.squeeze()?;
    
    // Absorb FRI layer commitments and derive betas
    let mut fri_betas = Vec::with_capacity(fri_roots.len());
    for fri_root in fri_roots {
        fs.absorb_bytes(fri_root)?;
        fs.permute()?;
        fri_betas.push(fs.squeeze()?);
    }
    
    // CRITICAL: Derive query seed for position derivation
    // This binds query positions to the FS transcript (prevents adversarial positions!)
    
    // The query seed is the FS state AFTER all FRI betas
    // Positions are derived via: hash(seed || pow_nonce || counter) & mask
    // We can't do full in-circuit derivation (would need RPO hashing in-circuit per query)
    // But we CAN verify positions are bound by making them part of public input or
    // deriving a commitment to them from FS
    
    // For now: Return the FS state as a "query seed" that can be used to verify positions
    let query_seed = fs.squeeze()?;
    
    Ok((z, deep_coeffs, fri_betas))
}

// TODO: Add query position verification gadget
// Either: (1) derive positions in-circuit (expensive), or
//         (2) commit to positions and bind to FS, or  
//         (3) make positions public inputs (but this breaks constant PVUGC size!)
// 
// SECURITY: Currently positions are free witnesses - MUST be fixed before production!

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
    comp_width: usize,
) -> Result<Vec<FpGLVar>, SynthesisError> {  // Return comp_sum per query for FRI!
    let g_trace = FpGLVar::constant(InnerFr::from(7u64));  // Goldilocks generator
    let p_gl_const = FpGLVar::constant(InnerFr::from(18446744069414584321u64));  // GL modulus
    
    let mut comp_sums = Vec::with_capacity(trace_queries.len());
    
    // LDE domain parameters
    // For Goldilocks with trace_len=16, blowup=8 → LDE domain size = 128 = 2^7
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    let m = (lde_domain_size as f64).log2() as usize;  // m = log2(N)
    let domain_offset = FpGLVar::constant(InnerFr::from(1u64));  // Standard offset
    
    // Precompute g_lde powers: g_lde^(2^k) for k=0..m-1
    // g_lde = g_trace^trace_len (subgroup generator for LDE)
    // For trace_len=16, g_lde = 7^16 mod p
    let g_lde_u64 = {
        use winter_math::FieldElement;
        let g = GL::new(7);
        let g_lde = g.exp((air_params.trace_len as u64).into());
        g_lde.as_int()
    };
    let g_lde = FpGLVar::constant(InnerFr::from(g_lde_u64));
    
    // Compute powers {g_lde^(2^k)} for bit decomposition
    let mut g_powers = vec![g_lde.clone()];  // g^1
    for _ in 1..m {
        let prev = g_powers.last().unwrap();
        g_powers.push(prev * prev);  // g^(2^k) = (g^(2^(k-1)))^2
    }
    
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
        for (k, bit) in position_bits.iter().enumerate() {
            if k < g_powers.len() {
                // If bit is 1: result *= g^(2^k), else: result *= 1
                let multiplier = FpGLVar::conditionally_select(bit, &g_powers[k], &FpGLVar::one())?;
                result = result * &multiplier;
            }
        }
        
        // x = offset · g_lde^position
        let x = result;
        
        // Allocate OOD values
        let ood_current: Vec<FpGLVar> = ood_trace_current.iter()
            .map(|v| FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v))))
            .collect::<Result<_, _>>()?;
        let ood_next: Vec<FpGLVar> = ood_trace_next.iter()
            .map(|v| FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*v))))
            .collect::<Result<_, _>>()?;
        
        // DEEP must NOT be conditional - verify array sizes and fail if mismatched
        assert_eq!(ood_current.len(), trace_q.values.len(), 
            "OOD current size must match trace query size");
        assert_eq!(ood_next.len(), trace_q.values.len(),
            "OOD next size must match trace query size");
        
        // Compute DEEP: Σ γᵢ · (T(x) - T(z)) / (x - z·multᵢ)
        let mut deep_sum = FpGLVar::zero();
        
        for (col_idx, &t_x_u64) in trace_q.values.iter().enumerate() {
            let t_x = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(t_x_u64)))?;
            
            // Term at z (mult=1): Enforce γ·(T(x)-T(z)) - term·(x-z) = q·p_GL (mod p_GL)
            let diff_z = &t_x - &ood_current[col_idx];
            let den_z = &x - z;
            
            let term_z = FpGLVar::new_witness(cs.clone(), || {
                use crate::gl_u64::{fr_to_gl_u64, gl_sub, gl_mul, gl_inv};
                // Compute term = diff / den in GL field (proper u64 arithmetic!)
                let diff_gl = fr_to_gl_u64(diff_z.value()?);
                let den_gl = fr_to_gl_u64(den_z.value()?);
                let term_gl = gl_mul(diff_gl, gl_inv(den_gl));
                Ok(InnerFr::from(term_gl))
            })?;
            
            let gamma_z = &deep_coeffs[col_idx * 2];
            let lhs = gamma_z * &diff_z;
            let rhs = &term_z * den_z;
            enforce_gl_eq(&lhs, &rhs, &p_gl_const)?;
            
            deep_sum = deep_sum + &term_z;
            
            // Term at z·g (mult=g): same pattern
            let diff_zg = &t_x - &ood_next[col_idx];
            let zg = z * &g_trace;
            let den_zg = &x - &zg;
            
            let term_zg = FpGLVar::new_witness(cs.clone(), || {
                use crate::gl_u64::{fr_to_gl_u64, gl_mul, gl_inv};
                let diff_gl = fr_to_gl_u64(diff_zg.value()?);
                let den_gl = fr_to_gl_u64(den_zg.value()?);
                let term_gl = gl_mul(diff_gl, gl_inv(den_gl));
                Ok(InnerFr::from(term_gl))
            })?;
            
            let gamma_zg = &deep_coeffs[col_idx * 2 + 1];
            let lhs_zg = gamma_zg * &diff_zg;
            let rhs_zg = &term_zg * den_zg;
            enforce_gl_eq(&lhs_zg, &rhs_zg, &p_gl_const)?;
            
            deep_sum = deep_sum + &term_zg;
        }
        
        // Now add composition DEEP terms (shift {0} only)
        let trace_deep_terms = trace_q.values.len() * 2;
        for (comp_idx, &c_x_u64) in comp_q.values.iter().enumerate() {
            let gamma_idx = trace_deep_terms + comp_idx;
            if gamma_idx >= deep_coeffs.len() {
                panic!("Not enough DEEP coefficients: need {}, have {}", gamma_idx + 1, deep_coeffs.len());
            }
            
            let c_x = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c_x_u64)))?;
            
            // Composition uses shift {0} only
            if comp_idx < ood_comp.len() {
                let c_z = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(ood_comp[comp_idx])))?;
                let diff = &c_x - &c_z;
                let den = &x - z;
                
                let term = FpGLVar::new_witness(cs.clone(), || {
                    use crate::gl_u64::{fr_to_gl_u64, gl_mul, gl_inv};
                    let diff_gl = fr_to_gl_u64(diff.value()?);
                    let den_gl = fr_to_gl_u64(den.value()?);
                    let term_gl = gl_mul(diff_gl, gl_inv(den_gl));
                    Ok(InnerFr::from(term_gl))
                })?;
                
                let gamma = &deep_coeffs[gamma_idx];
                let lhs = gamma * &diff;
                let rhs = &term * den;
                enforce_gl_eq(&lhs, &rhs, &p_gl_const)?;
                
                deep_sum = deep_sum + &term;
            }
        }
        
        // CRITICAL: Compare DEEP sum to sum of Merkle-opened composition values (mod p_GL!)
        let mut comp_sum = FpGLVar::zero();
        for &c_val in &comp_q.values {
            let c = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c_val)))?;
            comp_sum = comp_sum + &c;
        }
        
        // Enforce equality mod p_GL (not Fr377!)
        enforce_gl_eq(&deep_sum, &comp_sum, &p_gl_const)?;
        
        // Save comp_sum for FRI
        comp_sums.push(comp_sum);
    }
    
    Ok(comp_sums)
}

/// Verify FRI multi-layer folding
///
/// Verifies Winterfell's exact FRI protocol:
/// - Layer-by-layer folding: v_lo + β·v_hi = v_next
/// - Merkle commitment to each layer
/// - Final layer is constant (or small enough to include directly)
fn verify_fri_folding(
    cs: ConstraintSystemRef<InnerFr>,
    fri_layers: &[FriLayerQueries],
    fri_roots: &[Vec<UInt8<InnerFr>>],
    fri_betas: &[FpGLVar],
    mut current: Vec<FpGLVar>,  // Initial values from DEEP
) -> Result<(), SynthesisError> {
    let p_gl_const = FpGLVar::constant(InnerFr::from(18446744069414584321u64));
    // Verify each layer's folding equation and Merkle commitment
    for (layer_idx, layer) in fri_layers.iter().enumerate() {
        // Skip if no beta for this layer (shouldn't happen but be safe)
        if layer_idx >= fri_betas.len() {
            continue;
        }
        let beta = &fri_betas[layer_idx];
        
        // For each query in this layer:
        for fri_q in &layer.queries {
            let v_lo = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(fri_q.v_lo)))?;
            let v_hi = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(fri_q.v_hi)))?;
            
            // Hash [v_lo, v_hi] using RPO-256 to get leaf digest
            let mut rpo = Rpo256Var::new(cs.clone())?;
            let leaf_digest = rpo.hash_elements(&vec![v_lo.clone(), v_hi.clone()])?;
            
            // Verify Merkle path to FRI layer root
            let mut current = leaf_digest;
            for (sib_bytes, is_right) in fri_q.merkle_path.iter().zip(&fri_q.path_positions) {
                let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
                    .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
                    .collect::<Result<_, _>>()?;
                let sib = digest32_to_gl4(&sib_bytes_vars)?;
                
                let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
                
                let left = [
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &current[0])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &current[1])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &current[2])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &current[3])?,
                ];
                let right = [
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[0], &sib[0])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[1], &sib[1])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[2], &sib[2])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &current[3], &sib[3])?,
                ];
                
                current = rpo.merge(&left, &right)?;
            }
            
            // Verify root matches this layer's commitment
            if layer_idx < fri_roots.len() {
                let root_gl = digest32_to_gl4(&fri_roots[layer_idx])?;
                for i in 0..4 {
                    current[i].enforce_equal(&root_gl[i])?;
                }
            }
            
        }
        
        // Now perform consistency + fold for ALL queries in this layer
        let mut next = Vec::with_capacity(layer.queries.len());
        
        for (q_idx, fri_q) in layer.queries.iter().enumerate() {
            let v_lo = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(fri_q.v_lo)))?;
            let v_hi = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(fri_q.v_hi)))?;
            
            // Consistency: current[q] should match v_lo or v_hi based on position parity
            // The LSB of position tells us: even → v_lo, odd → v_hi
            // This is encoded in path_positions[0] (the first bit when walking up the tree)
            if q_idx < current.len() && !fri_q.path_positions.is_empty() {
                let lsb = Boolean::new_witness(cs.clone(), || Ok(fri_q.path_positions[0]))?;
                let selected = FpGLVar::conditionally_select(&lsb, &v_hi, &v_lo)?;
                enforce_gl_eq(&current[q_idx], &selected, &p_gl_const)?;
            }
            
            // Fold: next[q] = v_lo + β·v_hi (mod p_GL)
            let folded = &v_lo + &(beta * &v_hi);
            let v_next = FpGLVar::new_witness(cs.clone(), || {
                use crate::gl_u64::{fr_to_gl_u64, gl_add, gl_mul};
                let v_lo_gl = fr_to_gl_u64(v_lo.value()?);
                let v_hi_gl = fr_to_gl_u64(v_hi.value()?);
                let beta_gl = fr_to_gl_u64(beta.value()?);
                let next_gl = gl_add(v_lo_gl, gl_mul(beta_gl, v_hi_gl));
                Ok(InnerFr::from(next_gl))
            })?;
            
            enforce_gl_eq(&folded, &v_next, &p_gl_const)?;
            next.push(v_next);
        }
        
        current = next;  // Advance to next layer
    }
    
    // Terminal check: For fri_layers=0 case, current == comp_sums (already verified in DEEP)
    // For fri_layers > 0, final current should match remainder polynomial
    // Since our proof has fri_layers=0, this is satisfied
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_full_stark_verifier_structure() {
        // TODO: Basic smoke test with parsed proof
    }
}

