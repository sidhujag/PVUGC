//! OOD Equation Verification in R1CS
//!
//! This module implements the Out-of-Domain (OOD) equation verification
//! for the VerifierAir in R1CS constraints. It hardcodes all 27 VerifierAir
//! constraint evaluations and verifies:
//!
//!   transition_sum * exemption + boundary_contributions = C(z) * zerofier_num
//!
//! This binds the composition polynomial to the actual AIR constraints,
//! ensuring the proof is for VerifierAir specifically.

use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use super::inner_stark_full::{AirParams, enforce_gl_eq};
use super::gadgets::gl_fast::{
    GlVar, gl_add_light, gl_mul_light, gl_sub_light,
};
// Use Winterfell's actual Rp64_256 constants to match the AIR exactly
use winter_crypto::hashers::Rp64_256;

// Type alias for field variable
type FpGLVar = ark_r1cs_std::fields::fp::FpVar<InnerFr>;

// Use the same InnerFr as inner_stark_full
type InnerFr = ark_bls12_377::Fr;

// ============================================================================
// PUBLIC API
// ============================================================================

/// Verify the OOD equation in-circuit.
///
/// 1. VDF STARK → Aggregator STARK → VerifierSTARK → Groth16
/// 2. At each Winterfell verification step, AIR constraints ARE checked
/// 3. The VerifierSTARK's constraints (VerifierAir) include fri[6] == fri[7]
/// 4. Winterfell verifies this BEFORE we parse for Groth16
///
/// This binds the composition polynomial to the actual AIR constraints,
/// ensuring the proof is for VerifierAir specifically.
pub fn verify_ood_equation_in_circuit(
    cs: ConstraintSystemRef<InnerFr>,
    ood_trace_current: &[GlVar],
    ood_trace_next: &[GlVar],
    ood_comp: &[GlVar],
    z: &FpGLVar,
    constraint_coeffs: &[FpGLVar],
    air_params: &AirParams,
) -> Result<(), SynthesisError> {
    const NUM_TRANSITION_CONSTRAINTS: usize = 27;
    
    if ood_trace_current.len() < NUM_TRANSITION_CONSTRAINTS || ood_trace_next.len() < NUM_TRANSITION_CONSTRAINTS {
        return Err(SynthesisError::Unsatisfiable);
    }
    if constraint_coeffs.len() < NUM_TRANSITION_CONSTRAINTS + 5 {
        return Err(SynthesisError::Unsatisfiable);
    }
    
    let z_gl = GlVar(z.clone());
    let trace_len = air_params.trace_len;
    let g_trace = air_params.g_trace;
    let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    let zero = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
    
    // =========================================================================
    // STEP 1: Compute domain values
    // =========================================================================
    let z_pow_n = gl_pow(cs.clone(), &z_gl, trace_len)?;
    let zerofier_num = gl_sub_light(cs.clone(), &z_pow_n, &one)?;
    let g_pow_n_minus_1 = mod_pow_goldilocks(g_trace, (trace_len - 1) as u64);
    let g_pow_n_minus_1_gl = GlVar(FpGLVar::constant(InnerFr::from(g_pow_n_minus_1)));
    let exemption = gl_sub_light(cs.clone(), &z_gl, &g_pow_n_minus_1_gl)?;
    let z_minus_1 = gl_sub_light(cs.clone(), &z_gl, &one)?;
    
    // =========================================================================
    // STEP 2: Evaluate all 27 VerifierAir transition constraints (HARDCODED)
    // =========================================================================
    let constraints = evaluate_verifier_air_constraints_gl(
        cs.clone(), ood_trace_current, ood_trace_next
    )?;
    
    // =========================================================================
    // STEP 3: Compute transition_sum = Σ α_i * c_i(z)
    // =========================================================================
    let mut transition_sum = zero.clone();
    for (i, constraint) in constraints.iter().enumerate() {
        let coeff = GlVar(constraint_coeffs[i].clone());
        let weighted = gl_mul_light(cs.clone(), &coeff, constraint)?;
        transition_sum = gl_add_light(cs.clone(), &transition_sum, &weighted)?;
    }
    
    // =========================================================================
    // STEP 4: Compute C(z) = Σ ood_comp[i] * z^(i*n)
    // =========================================================================
    let mut c_combined = zero.clone();
    let mut z_pow_in = one.clone();
    for comp_i in ood_comp.iter() {
        let term = gl_mul_light(cs.clone(), comp_i, &z_pow_in)?;
        c_combined = gl_add_light(cs.clone(), &c_combined, &term)?;
        z_pow_in = gl_mul_light(cs.clone(), &z_pow_in, &z_pow_n)?;
    }
    
    // =========================================================================
    // STEP 5: Compute boundary contributions
    // sum_powers = zerofier_num / (z - 1)
    // trans_zerofier = zerofier_num / exemption
    // =========================================================================
    let initial_cols = [3usize, 4, 5, 6];
    let mut initial_sum = zero.clone();
    for (j, &col) in initial_cols.iter().enumerate() {
        let coeff_idx = NUM_TRANSITION_CONSTRAINTS + j;
        let beta = GlVar(constraint_coeffs[coeff_idx].clone());
        let val = &ood_trace_current[col];
        let term = gl_mul_light(cs.clone(), &beta, val)?;
        initial_sum = gl_add_light(cs.clone(), &initial_sum, &term)?;
    }
    
    let final_coeff_idx = NUM_TRANSITION_CONSTRAINTS + 4;
    let beta_final = GlVar(constraint_coeffs[final_coeff_idx].clone());
    let val_26 = &ood_trace_current[26];
    let val_minus_1 = gl_sub_light(cs.clone(), val_26, &one)?;
    let final_term = gl_mul_light(cs.clone(), &beta_final, &val_minus_1)?;
    
    // =========================================================================
    // STEP 6: Verify OOD equation (avoiding division by multiplying through)
    //
    // Original equation (from diagnostic):
    //   transition_sum * exemption + boundary_contrib = C(z) * zerofier_num
    //
    // Where:
    //   boundary_contrib = initial_sum * zerofier_num / (z-1) + final_term * zerofier_num / exemption
    //
    // Multiply both sides by (z-1) * exemption to eliminate divisions:
    //   transition_sum * exemption * (z-1) * exemption
    //     + initial_sum * zerofier_num * exemption 
    //     + final_term * zerofier_num * (z-1)
    //   = C(z) * zerofier_num * (z-1) * exemption
    //
    // Simplify:
    //   transition_sum * exemption² * (z-1) + initial_sum * zerofier_num * exemption + final_term * zerofier_num * (z-1)
    //   = C(z) * zerofier_num * (z-1) * exemption
    // =========================================================================
    
    // LHS part 1: transition_sum * exemption² * (z-1)
    let exemption_sq = gl_mul_light(cs.clone(), &exemption, &exemption)?;
    let trans_part = gl_mul_light(cs.clone(), &transition_sum, &exemption_sq)?;
    let lhs_part1 = gl_mul_light(cs.clone(), &trans_part, &z_minus_1)?;
    
    // LHS part 2: initial_sum * zerofier_num * exemption
    let init_temp = gl_mul_light(cs.clone(), &initial_sum, &zerofier_num)?;
    let lhs_part2 = gl_mul_light(cs.clone(), &init_temp, &exemption)?;
    
    // LHS part 3: final_term * zerofier_num * (z-1)
    let final_temp = gl_mul_light(cs.clone(), &final_term, &zerofier_num)?;
    let lhs_part3 = gl_mul_light(cs.clone(), &final_temp, &z_minus_1)?;
    
    // LHS = part1 + part2 + part3
    let lhs_12 = gl_add_light(cs.clone(), &lhs_part1, &lhs_part2)?;
    let lhs = gl_add_light(cs.clone(), &lhs_12, &lhs_part3)?;
    
    // RHS: C(z) * zerofier_num * (z-1) * exemption
    let rhs_temp1 = gl_mul_light(cs.clone(), &c_combined, &zerofier_num)?;
    let rhs_temp2 = gl_mul_light(cs.clone(), &rhs_temp1, &z_minus_1)?;
    let rhs = gl_mul_light(cs.clone(), &rhs_temp2, &exemption)?;
    
    enforce_gl_eq(&lhs.0, &rhs.0)?;
    
    Ok(())
}

// ============================================================================
// CONSTRAINT EVALUATION
// ============================================================================

/// Evaluate all 27 VerifierAir transition constraints at OOD point
/// 
/// This is the HARDCODED constraint evaluation matching constraints.rs exactly.
fn evaluate_verifier_air_constraints_gl(
    cs: ConstraintSystemRef<InnerFr>,
    current: &[GlVar],
    next: &[GlVar],
) -> Result<Vec<GlVar>, SynthesisError> {
    const NUM_SELECTORS: usize = 3;
    const HASH_STATE_START: usize = 3;
    const HASH_STATE_WIDTH: usize = 12;
    const FRI_START: usize = 15;
    const AUX_START: usize = 23;
    
    let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    let zero = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
    
    let mut constraints = Vec::with_capacity(27);
    
    // --- 1. Selector constraints (3): s * (s-1) = 0 [enforce_binary] ---
    for i in 0..NUM_SELECTORS {
        let s = &current[i];
        let s_minus_one = gl_sub_light(cs.clone(), s, &one)?;
        let c = gl_mul_light(cs.clone(), s, &s_minus_one)?;
        constraints.push(c);
    }
    
    // --- 2. Decode operations from selectors ---
    let (op, next_op) = decode_operations_gl(cs.clone(), current, next)?;
    
    // --- 3. Get current and next hash states ---
    let mut current_hash = Vec::with_capacity(HASH_STATE_WIDTH);
    let mut next_hash = Vec::with_capacity(HASH_STATE_WIDTH);
    for i in 0..HASH_STATE_WIDTH {
        current_hash.push(current[HASH_STATE_START + i].clone());
        next_hash.push(next[HASH_STATE_START + i].clone());
    }
    
    // --- 4. Get round counter and compute round constants via Lagrange ---
    // Matches AIR constraints.rs: uses Rp64_256::ARK1 and Rp64_256::ARK2
    let round_counter = &current[AUX_START]; // aux[0] = round counter
    let ark1 = compute_ark1_lagrange_gl(cs.clone(), round_counter)?;
    let ark2 = compute_ark2_lagrange_gl(cs.clone(), round_counter)?;
    
    // --- 5. Compute values for RPO round verification ---
    // Winterfell round: sbox → MDS → +ARK1 → inv_sbox → MDS → +ARK2
    // 
    // To verify without computing inv_sbox:
    // 1. Compute mid = MDS(sbox(current)) + ARK1
    // 2. Compute candidate = INV_MDS(next - ARK2)
    // 3. Verify: sbox(candidate) = mid (proves candidate = inv_sbox(mid))
    
    let mid = compute_rpo_mid_gl(cs.clone(), &current_hash, &ark1)?;
    
    // Compute next - ARK2
    let mut next_minus_ark2 = Vec::with_capacity(HASH_STATE_WIDTH);
    for i in 0..HASH_STATE_WIDTH {
        next_minus_ark2.push(gl_sub_light(cs.clone(), &next_hash[i], &ark2[i])?);
    }
    
    // Apply inverse MDS to get candidate
    let candidate = apply_inv_mds_gl(cs.clone(), &next_minus_ark2)?;
    
    // --- 6. Hash state constraints (12) ---
    for i in 0..HASH_STATE_WIDTH {
        // For Permute: verify sbox(candidate) = mid
        // This proves that candidate = inv_sbox(mid), validating the round
        let sbox_candidate = sbox_gl(cs.clone(), &candidate[i])?;
        let permute_constraint = gl_sub_light(cs.clone(), &sbox_candidate, &mid[i])?;
        
        // For Nop/Squeeze: next should equal current (copy)
        let copy_constraint = gl_sub_light(cs.clone(), &next_hash[i], &current_hash[i])?;
        
        // For Absorb: capacity preserved, rate can change
        let absorb_constraint = if i < 4 {
            // Capacity (first 4 elements): must be preserved
            gl_sub_light(cs.clone(), &next_hash[i], &current_hash[i])?
        } else {
            // Rate (elements 4-11): can change (allow any = 0)
            zero.clone()
        };
        
        // Combine constraints based on operation:
        // NOTE: Nop is padding after permute(), state may be modified after it,
        // so we allow any transition from Nop (like Init/Merkle/etc.)
        // constraint = is_permute * permute_constraint 
        //            + is_squeeze * copy_constraint
        //            + is_absorb * absorb_constraint
        //            + (is_init + is_merkle + is_fri + is_deep + is_nop) * 0
        let term1 = gl_mul_light(cs.clone(), &op.is_permute, &permute_constraint)?;
        
        // Only squeeze enforces copy (nop moved to allow_any)
        let term2 = gl_mul_light(cs.clone(), &op.is_squeeze, &copy_constraint)?;
        
        let term3 = gl_mul_light(cs.clone(), &op.is_absorb, &absorb_constraint)?;
        
        let sum12 = gl_add_light(cs.clone(), &term1, &term2)?;
        let constraint = gl_add_light(cs.clone(), &sum12, &term3)?;
        
        constraints.push(constraint);
    }
    
    // --- 7. FRI/DEEP working constraints (8) ---
    let op_special = {
        let t1 = gl_add_light(cs.clone(), &op.is_merkle, &op.is_fri)?;
        let t2 = gl_add_light(cs.clone(), &t1, &op.is_deep)?;
        let t3 = gl_add_light(cs.clone(), &t2, &op.is_init)?;
        gl_add_light(cs.clone(), &t3, &op.is_absorb)?
    };
    let next_special = {
        let t1 = gl_add_light(cs.clone(), &next_op.is_merkle, &next_op.is_fri)?;
        let t2 = gl_add_light(cs.clone(), &t1, &next_op.is_deep)?;
        gl_add_light(cs.clone(), &t2, &next_op.is_init)?
    };
    let one_minus_op_special = gl_sub_light(cs.clone(), &one, &op_special)?;
    let one_minus_next_special = gl_sub_light(cs.clone(), &one, &next_special)?;
    let both_not_special = gl_mul_light(cs.clone(), &one_minus_op_special, &one_minus_next_special)?;
    
    // FRI folding constraint: 2*x*g = x*(f_x + f_neg_x) + beta*(f_x - f_neg_x)
    let f_x = &current[FRI_START];
    let f_neg_x = &current[FRI_START + 1];
    let x = &current[FRI_START + 2];
    let beta = &current[FRI_START + 3];
    let g = &current[FRI_START + 4];
    let two = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
    let two_x = gl_mul_light(cs.clone(), &two, x)?;
    let fri_fold_lhs = gl_mul_light(cs.clone(), &two_x, g)?;
    let f_sum = gl_add_light(cs.clone(), f_x, f_neg_x)?;
    let f_diff = gl_sub_light(cs.clone(), f_x, f_neg_x)?;
    let x_f_sum = gl_mul_light(cs.clone(), x, &f_sum)?;
    let beta_f_diff = gl_mul_light(cs.clone(), beta, &f_diff)?;
    let fri_fold_rhs = gl_add_light(cs.clone(), &x_f_sum, &beta_f_diff)?;
    let fri_fold_constraint = gl_sub_light(cs.clone(), &fri_fold_lhs, &fri_fold_rhs)?;
    
    // OOD constraint: fri[6] - fri[7]
    let fri_6 = &current[FRI_START + 6];
    let fri_7 = &current[FRI_START + 7];
    let _ood_constraint = gl_sub_light(cs.clone(), fri_6, fri_7)?;
    
    // ========================================================================
    // DEEP COMPOSE VERIFICATION MODES (aux[2] determines mode)
    // 
    // aux[2] = 0: ROOT mode - hash_state[0..3] == fri[0..3]
    // aux[2] = 1: OOD mode - fri[6] == fri[7] (OOD LHS == RHS)
    // aux[2] = 2: TERMINAL mode - fri[6] == fri[7] (FRI final == expected)
    // aux[2] = 3: DEEP mode - fri[6] == fri[7] (DEEP computed == expected)
    // ========================================================================
    let aux_mode = &current[AUX_START + 2];
    
    // Equality constraint: fri[6] == fri[7] (used for OOD, TERMINAL, DEEP modes)
    let equality_constraint = gl_sub_light(cs.clone(), fri_6, fri_7)?;
    
    // Root verification constraints: hash_state[i] == fri[i] for i in 0..4
    let root_constraints: [GlVar; 4] = [
        gl_sub_light(cs.clone(), &current_hash[0], &current[FRI_START])?,
        gl_sub_light(cs.clone(), &current_hash[1], &current[FRI_START + 1])?,
        gl_sub_light(cs.clone(), &current_hash[2], &current[FRI_START + 2])?,
        gl_sub_light(cs.clone(), &current_hash[3], &current[FRI_START + 3])?,
    ];
    
    // Compute is_root_check = (aux[2] - 1) * (aux[2] - 2) * (aux[2] - 3)
    // When aux[2] = 0: (-1)*(-2)*(-3) = -6 (non-zero, check applies)
    // When aux[2] = 1,2,3: is_root_check = 0 (check doesn't apply)
    let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
    let three_gl = GlVar(FpGLVar::constant(InnerFr::from(3u64)));
    let aux_m1 = gl_sub_light(cs.clone(), aux_mode, &one)?;
    let aux_m2 = gl_sub_light(cs.clone(), aux_mode, &two_gl)?;
    let aux_m3 = gl_sub_light(cs.clone(), aux_mode, &three_gl)?;
    let is_root_check_temp = gl_mul_light(cs.clone(), &aux_m1, &aux_m2)?;
    let is_root_check = gl_mul_light(cs.clone(), &is_root_check_temp, &aux_m3)?;
    
    for i in 0..8 {
        let fri_curr = &current[FRI_START + i];
        let fri_next = &next[FRI_START + i];
        let copy_constraint = gl_sub_light(cs.clone(), fri_next, fri_curr)?;
        
        if i == 4 {
            // FRI column 4: FRI folding result
            // During FriFold: verify folding formula is correct
            let fri_term = gl_mul_light(cs.clone(), &op.is_fri, &fri_fold_constraint)?;
            let copy_term = gl_mul_light(cs.clone(), &both_not_special, &copy_constraint)?;
            let c = gl_add_light(cs.clone(), &fri_term, &copy_term)?;
            constraints.push(c);
        } else if i == 6 {
            // FRI column 6: EQUALITY VERIFICATION during DeepCompose
            // When aux[2] != 0: verify fri[6] == fri[7]
            // This covers OOD (mode 1), TERMINAL (mode 2), and DEEP (mode 3)
            // 
            // Constraint: op.is_deep * aux[2] * equality_constraint = 0
            // When aux[2] = 0, constraint is 0 (satisfied, root mode uses columns 0-3)
            // When aux[2] != 0, constraint requires equality_constraint = 0
            let deep_aux = gl_mul_light(cs.clone(), &op.is_deep, aux_mode)?;
            let ood_term = gl_mul_light(cs.clone(), &deep_aux, &equality_constraint)?;
            let copy_term = gl_mul_light(cs.clone(), &both_not_special, &copy_constraint)?;
            let c = gl_add_light(cs.clone(), &ood_term, &copy_term)?;
            constraints.push(c);
        } else if i < 4 {
            // FRI columns 0-3: ROOT VERIFICATION during DeepCompose (aux[2] = 0)
            // Constraint: hash_state[i] == fri[i]
            // ONLY enforce when in ROOT mode (aux[2] = 0)
            //
            // Constraint: op.is_deep * is_root_check * root_constraint = 0
            // When aux[2] = 0: is_root_check = -6, so constraint = -6 * root_constraint
            //                  For this to be 0, root_constraint must be 0 ✓
            // When aux[2] != 0: is_root_check = 0, constraint = 0 (trivially satisfied) ✓
            let deep_root = gl_mul_light(cs.clone(), &op.is_deep, &is_root_check)?;
            let root_term = gl_mul_light(cs.clone(), &deep_root, &root_constraints[i])?;
            let copy_term = gl_mul_light(cs.clone(), &both_not_special, &copy_constraint)?;
            let c = gl_add_light(cs.clone(), &root_term, &copy_term)?;
            constraints.push(c);
        } else {
            // FRI columns 5, 7: copy constraint only
            let c = gl_mul_light(cs.clone(), &both_not_special, &copy_constraint)?;
            constraints.push(c);
        }
    }
    
    // --- 8. Auxiliary constraints (4) ---
    for i in 0..4 {
        let aux_curr = &current[AUX_START + i];
        let aux_next = &next[AUX_START + i];
        
        if i == 0 {
            // Round counter constraint
            let rc = aux_curr;
            
            // Range check: rc ∈ {0,1,2,3,4,5,6} (degree 7)
            // rc * (rc-1) * (rc-2) * (rc-3) * (rc-4) * (rc-5) * (rc-6) = 0
            let rc_m1 = gl_sub_light(cs.clone(), rc, &one)?;
            let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
            let three_gl = GlVar(FpGLVar::constant(InnerFr::from(3u64)));
            let four_gl = GlVar(FpGLVar::constant(InnerFr::from(4u64)));
            let five_gl = GlVar(FpGLVar::constant(InnerFr::from(5u64)));
            let six_gl = GlVar(FpGLVar::constant(InnerFr::from(6u64)));
            let seven_gl = GlVar(FpGLVar::constant(InnerFr::from(7u64)));
            let rc_m2 = gl_sub_light(cs.clone(), rc, &two_gl)?;
            let rc_m3 = gl_sub_light(cs.clone(), rc, &three_gl)?;
            let rc_m4 = gl_sub_light(cs.clone(), rc, &four_gl)?;
            let rc_m5 = gl_sub_light(cs.clone(), rc, &five_gl)?;
            let rc_m6 = gl_sub_light(cs.clone(), rc, &six_gl)?;
            
            // Compute degree-7 product
            let p1 = gl_mul_light(cs.clone(), rc, &rc_m1)?;
            let p2 = gl_mul_light(cs.clone(), &p1, &rc_m2)?;
            let p3 = gl_mul_light(cs.clone(), &p2, &rc_m3)?;
            let p4 = gl_mul_light(cs.clone(), &p3, &rc_m4)?;
            let p5 = gl_mul_light(cs.clone(), &p4, &rc_m5)?;
            let rc_in_range = gl_mul_light(cs.clone(), &p5, &rc_m6)?;
            
            // Permute check: is_permute * rc_in_range
            let permute_check = gl_mul_light(cs.clone(), &op.is_permute, &rc_in_range)?;
            
            // Merkle binary check: is_merkle * rc * (rc - 1)
            let rc_binary = gl_mul_light(cs.clone(), rc, &rc_m1)?;
            let merkle_binary_check = gl_mul_light(cs.clone(), &op.is_merkle, &rc_binary)?;
            
            // Basic ops check: (is_nop + is_squeeze) * (rc - 7)
            let basic_ops = gl_add_light(cs.clone(), &op.is_nop, &op.is_squeeze)?;
            let rc_m7 = gl_sub_light(cs.clone(), rc, &seven_gl)?;
            let basic_check = gl_mul_light(cs.clone(), &basic_ops, &rc_m7)?;
            
            let c1 = gl_add_light(cs.clone(), &permute_check, &merkle_binary_check)?;
            let c = gl_add_light(cs.clone(), &c1, &basic_check)?;
            constraints.push(c);
        } else if i == 3 {
            // Acceptance flag: binary + monotonic
            // binary: next * (next - 1) [enforce_binary]
            // monotonic: curr * (1 - next)
            let next_m1 = gl_sub_light(cs.clone(), aux_next, &one)?;
            let binary = gl_mul_light(cs.clone(), aux_next, &next_m1)?;
            let one_minus_next = gl_sub_light(cs.clone(), &one, aux_next)?;
            let monotonic = gl_mul_light(cs.clone(), aux_curr, &one_minus_next)?;
            let c = gl_add_light(cs.clone(), &binary, &monotonic)?;
            constraints.push(c);
        } else {
            // Allow any for aux[1,2]
            constraints.push(zero.clone());
        }
    }
    
    Ok(constraints)
}

// ============================================================================
// RPO ROUND COMPUTATION IN R1CS (MATCHING AIR CONSTRAINTS EXACTLY)
// ============================================================================

/// Compute ARK1 constants using Lagrange interpolation on round_counter
/// Uses Winterfell's Rp64_256::ARK1 to match AIR constraints.rs exactly
fn compute_ark1_lagrange_gl(
    cs: ConstraintSystemRef<InnerFr>,
    round_counter: &GlVar,
) -> Result<Vec<GlVar>, SynthesisError> {
    let denom_inverses: [u64; 7] = precompute_lagrange_denominators();
    
    let mut ark1 = Vec::with_capacity(12);
    
    for i in 0..12 {
        let mut sum = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        
        for r in 0..7 {
            // Compute numerator: prod_{j!=r} (round_counter - j)
            let mut lagrange_num = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
            for j in 0..7 {
                if j != r {
                    let j_val = GlVar(FpGLVar::constant(InnerFr::from(j as u64)));
                    let diff = gl_sub_light(cs.clone(), round_counter, &j_val)?;
                    lagrange_num = gl_mul_light(cs.clone(), &lagrange_num, &diff)?;
                }
            }
            
            // L_r(round_counter) = numerator * denom_inverse[r]
            let denom_inv = GlVar(FpGLVar::constant(InnerFr::from(denom_inverses[r])));
            let lagrange_basis = gl_mul_light(cs.clone(), &lagrange_num, &denom_inv)?;
            
            // Contribution: ARK1[r][i] * L_r(round_counter)
            // Use Winterfell's ARK1 constants
            let ark1_val = Rp64_256::ARK1[r][i].as_int();
            let ark1_const = GlVar(FpGLVar::constant(InnerFr::from(ark1_val)));
            let contrib = gl_mul_light(cs.clone(), &ark1_const, &lagrange_basis)?;
            sum = gl_add_light(cs.clone(), &sum, &contrib)?;
        }
        
        ark1.push(sum);
    }
    
    Ok(ark1)
}

/// Compute ARK2 constants using Lagrange interpolation on round_counter
/// Uses Winterfell's Rp64_256::ARK2 to match AIR constraints.rs exactly
fn compute_ark2_lagrange_gl(
    cs: ConstraintSystemRef<InnerFr>,
    round_counter: &GlVar,
) -> Result<Vec<GlVar>, SynthesisError> {
    let denom_inverses: [u64; 7] = precompute_lagrange_denominators();
    
    let mut ark2 = Vec::with_capacity(12);
    
    for i in 0..12 {
        let mut sum = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        
        for r in 0..7 {
            // Compute Lagrange basis polynomial value
            let mut lagrange_num = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
            for j in 0..7 {
                if j != r {
                    let j_val = GlVar(FpGLVar::constant(InnerFr::from(j as u64)));
                    let diff = gl_sub_light(cs.clone(), round_counter, &j_val)?;
                    lagrange_num = gl_mul_light(cs.clone(), &lagrange_num, &diff)?;
                }
            }
            
            let denom_inv = GlVar(FpGLVar::constant(InnerFr::from(denom_inverses[r])));
            let lagrange_basis = gl_mul_light(cs.clone(), &lagrange_num, &denom_inv)?;
            
            // Use Winterfell's ARK2 constants
            let ark2_val = Rp64_256::ARK2[r][i].as_int();
            let ark2_const = GlVar(FpGLVar::constant(InnerFr::from(ark2_val)));
            let contrib = gl_mul_light(cs.clone(), &ark2_const, &lagrange_basis)?;
            sum = gl_add_light(cs.clone(), &sum, &contrib)?;
        }
        
        ark2.push(sum);
    }
    
    Ok(ark2)
}

/// Compute mid = MDS(sbox(current)) + ARK1
/// This is the first half of Winterfell's RPO round
fn compute_rpo_mid_gl(
    cs: ConstraintSystemRef<InnerFr>,
    state: &[GlVar],
    ark1: &[GlVar],
) -> Result<Vec<GlVar>, SynthesisError> {
    // Step 1: Apply S-box (x^7) to all elements
    let mut after_sbox = Vec::with_capacity(12);
    for i in 0..12 {
        after_sbox.push(sbox_gl(cs.clone(), &state[i])?);
    }
    
    // Step 2: Apply MDS matrix using Winterfell's constants
    let mut after_mds = Vec::with_capacity(12);
    for i in 0..12 {
        let mut sum = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        for j in 0..12 {
            let mds_val = Rp64_256::MDS[i][j].as_int();
            let mds_const = GlVar(FpGLVar::constant(InnerFr::from(mds_val)));
            let prod = gl_mul_light(cs.clone(), &mds_const, &after_sbox[j])?;
            sum = gl_add_light(cs.clone(), &sum, &prod)?;
        }
        after_mds.push(sum);
    }
    
    // Step 3: Add ARK1 constants
    let mut result = Vec::with_capacity(12);
    for i in 0..12 {
        result.push(gl_add_light(cs.clone(), &after_mds[i], &ark1[i])?);
    }
    
    Ok(result)
}

/// Apply inverse MDS matrix using Winterfell's INV_MDS constants
fn apply_inv_mds_gl(
    cs: ConstraintSystemRef<InnerFr>,
    state: &[GlVar],
) -> Result<Vec<GlVar>, SynthesisError> {
    let mut result = Vec::with_capacity(12);
    
    for i in 0..12 {
        let mut sum = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
        for j in 0..12 {
            let inv_mds_val = Rp64_256::INV_MDS[i][j].as_int();
            let inv_mds_const = GlVar(FpGLVar::constant(InnerFr::from(inv_mds_val)));
            let prod = gl_mul_light(cs.clone(), &inv_mds_const, &state[j])?;
            sum = gl_add_light(cs.clone(), &sum, &prod)?;
        }
        result.push(sum);
    }
    
    Ok(result)
}

/// Pre-compute 1 / prod_{j!=r} (r - j) for Lagrange interpolation
fn precompute_lagrange_denominators() -> [u64; 7] {
    const GL_MOD: u64 = 0xFFFFFFFF00000001;
    
    let mut denoms = [0u64; 7];
    for r in 0..7i64 {
        let mut prod: i64 = 1;
        for j in 0..7i64 {
            if j != r {
                prod *= r - j;
            }
        }
        // Convert to positive and compute inverse
        let prod_mod = if prod < 0 {
            GL_MOD - ((-prod) as u64 % GL_MOD)
        } else {
            prod as u64 % GL_MOD
        };
        denoms[r as usize] = mod_inverse_goldilocks(prod_mod);
    }
    denoms
}

/// Modular inverse in Goldilocks field using Fermat's little theorem
fn mod_inverse_goldilocks(a: u64) -> u64 {
    const GL_MOD: u64 = 0xFFFFFFFF00000001;
    // a^{p-2} mod p
    mod_pow_goldilocks(a, GL_MOD - 2)
}

/// S-box: x^7 in R1CS
fn sbox_gl(cs: ConstraintSystemRef<InnerFr>, x: &GlVar) -> Result<GlVar, SynthesisError> {
    let x2 = gl_mul_light(cs.clone(), x, x)?;
    let x4 = gl_mul_light(cs.clone(), &x2, &x2)?;
    let x3 = gl_mul_light(cs.clone(), &x2, x)?;
    let x7 = gl_mul_light(cs.clone(), &x4, &x3)?;
    Ok(x7)
}

// ============================================================================
// OPERATION DECODING
// ============================================================================

/// Decoded operation flags in GL field
struct DecodedOpGL {
    is_init: GlVar,
    is_absorb: GlVar,
    is_permute: GlVar,
    is_squeeze: GlVar,
    is_merkle: GlVar,
    is_fri: GlVar,
    is_deep: GlVar,
    is_nop: GlVar,
}

/// Decode 3-bit selectors into operation flags
fn decode_operations_gl(
    cs: ConstraintSystemRef<InnerFr>,
    current: &[GlVar],
    next: &[GlVar],
) -> Result<(DecodedOpGL, DecodedOpGL), SynthesisError> {
    let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    
    let decode_one = |s0: &GlVar, s1: &GlVar, s2: &GlVar| -> Result<DecodedOpGL, SynthesisError> {
        let not_s0 = gl_sub_light(cs.clone(), &one, s0)?;
        let not_s1 = gl_sub_light(cs.clone(), &one, s1)?;
        let not_s2 = gl_sub_light(cs.clone(), &one, s2)?;
        
        // is_init = (1-s2) * (1-s1) * (1-s0)
        let t1 = gl_mul_light(cs.clone(), &not_s2, &not_s1)?;
        let is_init = gl_mul_light(cs.clone(), &t1, &not_s0)?;
        
        // is_absorb = (1-s2) * (1-s1) * s0
        let is_absorb = gl_mul_light(cs.clone(), &t1, s0)?;
        
        // is_permute = (1-s2) * s1 * (1-s0)
        let t2 = gl_mul_light(cs.clone(), &not_s2, s1)?;
        let is_permute = gl_mul_light(cs.clone(), &t2, &not_s0)?;
        
        // is_squeeze = (1-s2) * s1 * s0
        let is_squeeze = gl_mul_light(cs.clone(), &t2, s0)?;
        
        // is_merkle = s2 * (1-s1) * (1-s0)
        let t3 = gl_mul_light(cs.clone(), s2, &not_s1)?;
        let is_merkle = gl_mul_light(cs.clone(), &t3, &not_s0)?;
        
        // is_fri = s2 * (1-s1) * s0
        let is_fri = gl_mul_light(cs.clone(), &t3, s0)?;
        
        // is_deep = s2 * s1 * (1-s0)
        let t4 = gl_mul_light(cs.clone(), s2, s1)?;
        let is_deep = gl_mul_light(cs.clone(), &t4, &not_s0)?;
        
        // is_nop = s2 * s1 * s0
        let is_nop = gl_mul_light(cs.clone(), &t4, s0)?;
        
        Ok(DecodedOpGL { is_init, is_absorb, is_permute, is_squeeze, is_merkle, is_fri, is_deep, is_nop })
    };
    
    let op = decode_one(&current[0], &current[1], &current[2])?;
    let next_op = decode_one(&next[0], &next[1], &next[2])?;
    
    Ok((op, next_op))
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Compute base^exp mod Goldilocks prime (native computation for constants)
pub fn mod_pow_goldilocks(base: u64, exp: u64) -> u64 {
    const P: u64 = 0xFFFFFFFF00000001u64;
    let mut result: u128 = 1;
    let mut b: u128 = base as u128;
    let mut e = exp;
    
    while e > 0 {
        if e & 1 == 1 {
            result = (result * b) % (P as u128);
        }
        b = (b * b) % (P as u128);
        e >>= 1;
    }
    result as u64
}

/// Compute z^exp using repeated squaring in GL field
pub fn gl_pow(
    cs: ConstraintSystemRef<InnerFr>,
    base: &GlVar,
    exp: usize,
) -> Result<GlVar, SynthesisError> {
    if exp == 0 {
        return Ok(GlVar(FpGLVar::constant(InnerFr::from(1u64))));
    }
    if exp == 1 {
        return Ok(base.clone());
    }
    
    let mut result = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    let mut current = base.clone();
    let mut n = exp;
    
    while n > 0 {
        if n & 1 == 1 {
            result = gl_mul_light(cs.clone(), &result, &current)?;
        }
        current = gl_mul_light(cs.clone(), &current, &current)?;
        n >>= 1;
    }
    
    Ok(result)
}
