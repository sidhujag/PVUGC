//! OOD Equation Verification in R1CS
//!
//! This module implements the Out-of-Domain (OOD) equation verification
//! for the VerifierAir in R1CS constraints. It hardcodes all VerifierAir
//! constraint evaluations and verifies:
//!
//!   transition_sum * exemption + boundary_contributions = C(z) * zerofier_num
//!
//! This binds the composition polynomial to the actual AIR constraints,
//! ensuring the proof is for VerifierAir specifically.

use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::alloc::AllocVar;
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
    stark_pub_inputs: &[u64], // Verifier AIR public inputs (statement_hash is first 4 elements)
) -> Result<(), SynthesisError> {
    // VerifierAir transition constraints count (must match `verifier_air/mod.rs` degrees length).
    const NUM_TRANSITION_CONSTRAINTS: usize = 34;
    
    if ood_trace_current.len() < NUM_TRANSITION_CONSTRAINTS || ood_trace_next.len() < NUM_TRANSITION_CONSTRAINTS {
        return Err(SynthesisError::Unsatisfiable);
    }
    // Need 34 transition + 8 boundary (4 capacity + 2 initial aux + 2 final aux)
    if constraint_coeffs.len() < NUM_TRANSITION_CONSTRAINTS + 8 {
        return Err(SynthesisError::Unsatisfiable);
    }
    
    // Extract statement_hash from public inputs (first 4 elements)
    let statement_hash: [u64; 4] = if stark_pub_inputs.len() >= 4 {
        [stark_pub_inputs[0], stark_pub_inputs[1], stark_pub_inputs[2], stark_pub_inputs[3]]
    } else {
        return Err(SynthesisError::Unsatisfiable);
    };
    
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
    
    // Extract params_digest from public inputs.
    //
    // Layout tail (last 4 u64s):
    //   params_digest (4)
    // 
    // SECURITY: Must require minimum length to ensure fields don't overlap.
    let pub_len = stark_pub_inputs.len();
    if pub_len < 8 {
        return Err(SynthesisError::Unsatisfiable);
    }
    
    let params_digest: [u64; 4] = [
        stark_pub_inputs[pub_len - 4],
        stark_pub_inputs[pub_len - 3],
        stark_pub_inputs[pub_len - 2],
        stark_pub_inputs[pub_len - 1],
    ];
    
    // =========================================================================
    // STEP 2: Evaluate all VerifierAir transition constraints (HARDCODED)
    // =========================================================================
    // Extract commitments from public inputs (see `VerifierPublicInputs::to_elements()` layout).
    if pub_len < 12 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let trace_commitment: [u64; 4] = [
        stark_pub_inputs[4],
        stark_pub_inputs[5],
        stark_pub_inputs[6],
        stark_pub_inputs[7],
    ];
    let comp_commitment: [u64; 4] = [
        stark_pub_inputs[8],
        stark_pub_inputs[9],
        stark_pub_inputs[10],
        stark_pub_inputs[11],
    ];
    // FRI commitments begin at index 12, and end before the final 10 tail elements.
    // We keep fixed shape by reading up to MAX_FRI_LAYERS and padding missing with zeros.
    const MAX_FRI_LAYERS: usize = 32;
    let fri_commitments_start = 12usize;
    let fri_commitments_end = pub_len.checked_sub(10).ok_or(SynthesisError::Unsatisfiable)?;
    if fri_commitments_end < fri_commitments_start {
        return Err(SynthesisError::Unsatisfiable);
    }
    let fri_commitments_words = fri_commitments_end - fri_commitments_start;
    if fri_commitments_words % 4 != 0 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let fri_commitments_len = (fri_commitments_words / 4).min(MAX_FRI_LAYERS);
    let mut fri_commitments: Vec<[u64; 4]> = Vec::with_capacity(MAX_FRI_LAYERS);
    for i in 0..MAX_FRI_LAYERS {
        if i < fri_commitments_len {
            let off = fri_commitments_start + 4 * i;
            fri_commitments.push([
                stark_pub_inputs[off],
                stark_pub_inputs[off + 1],
                stark_pub_inputs[off + 2],
                stark_pub_inputs[off + 3],
            ]);
        } else {
            fri_commitments.push([0u64; 4]);
        }
    }

    let constraints = evaluate_verifier_air_constraints_gl(
        cs.clone(),
        ood_trace_current,
        ood_trace_next,
        &statement_hash,
        &trace_commitment,
        &comp_commitment,
        &fri_commitments,
        &params_digest,
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
    // 
    // AIR has 8 boundary assertions (VerifierAir):
    //   - 4 initial capacity zeros (columns 3,4,5,6 at row 0) -> coeffs 34..37
    //   - 1 initial aux[1] = 0 (column 31 at row 0) -> coeff 38
    //   - 1 initial aux[3] = 0 (column 33 at row 0) -> coeff 39
    //   - 1 final aux[1] = expected_mode_counter (column 31 at last row) -> coeff 40
    //   - 1 final aux[3] = expected_checkpoint_count (column 33 at last row) -> coeff 41
    // =========================================================================
    
    // Initial capacity zeros (columns 3-6)
    let initial_cols = [3usize, 4, 5, 6];
    let mut initial_sum = zero.clone();
    for (j, &col) in initial_cols.iter().enumerate() {
        let coeff_idx = NUM_TRANSITION_CONSTRAINTS + j;
        let beta = GlVar(constraint_coeffs[coeff_idx].clone());
        let val = &ood_trace_current[col];
        let term = gl_mul_light(cs.clone(), &beta, val)?;
        initial_sum = gl_add_light(cs.clone(), &initial_sum, &term)?;
    }
    
    // Initial aux[1] = 0 (column 31)
    // (Matches AIR assertion order: capacity[0-3], then aux[1], then aux[3])
    let initial_aux1_coeff_idx = NUM_TRANSITION_CONSTRAINTS + 4;
    let beta_aux1_init = GlVar(constraint_coeffs[initial_aux1_coeff_idx].clone());
    let val_31 = &ood_trace_current[31];
    let aux1_init_term = gl_mul_light(cs.clone(), &beta_aux1_init, val_31)?;
    initial_sum = gl_add_light(cs.clone(), &initial_sum, &aux1_init_term)?;
    
    // Initial aux[3] = 0 (column 33)
    let initial_aux3_coeff_idx = NUM_TRANSITION_CONSTRAINTS + 5;
    let beta_aux3_init = GlVar(constraint_coeffs[initial_aux3_coeff_idx].clone());
    let val_33 = &ood_trace_current[33];
    let aux3_init_term = gl_mul_light(cs.clone(), &beta_aux3_init, val_33)?;
    initial_sum = gl_add_light(cs.clone(), &initial_sum, &aux3_init_term)?;
    
    // Final aux[1] = expected_mode_counter (column 31)
    // Layout: [..., expected_checkpoint_count, expected_mode_counter, interpreter_hash[0..4]]
    // So expected_mode_counter is at position pub_len - 5
    let expected_mode_counter = stark_pub_inputs[pub_len - 5];
    // IMPORTANT (universality): do not embed per-proof pub inputs as R1CS constants.
    let expected_mode_counter_gl = GlVar(FpGLVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(expected_mode_counter))
    })?);
    
    let final_aux1_coeff_idx = NUM_TRANSITION_CONSTRAINTS + 6;
    let beta_aux1_final = GlVar(constraint_coeffs[final_aux1_coeff_idx].clone());
    let val_31_minus_expected = gl_sub_light(cs.clone(), val_31, &expected_mode_counter_gl)?;
    let aux1_final_term = gl_mul_light(cs.clone(), &beta_aux1_final, &val_31_minus_expected)?;
    
    // Final aux[3] = expected_checkpoint_count (column 33)
    // expected_checkpoint_count is at position pub_len - 6
    let expected_checkpoints = stark_pub_inputs[pub_len - 6];
    let expected_checkpoints_gl = GlVar(FpGLVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(expected_checkpoints))
    })?);
    
    let final_aux3_coeff_idx = NUM_TRANSITION_CONSTRAINTS + 7;
    let beta_aux3_final = GlVar(constraint_coeffs[final_aux3_coeff_idx].clone());
    let val_33_minus_expected = gl_sub_light(cs.clone(), val_33, &expected_checkpoints_gl)?;
    let aux3_final_term = gl_mul_light(cs.clone(), &beta_aux3_final, &val_33_minus_expected)?;
    
    // Combine both final terms
    let final_term = gl_add_light(cs.clone(), &aux1_final_term, &aux3_final_term)?;
    
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

/// Evaluate all VerifierAir transition constraints at OOD point
///
/// This is the HARDCODED constraint evaluation matching constraints.rs exactly.
fn evaluate_verifier_air_constraints_gl(
    cs: ConstraintSystemRef<InnerFr>,
    current: &[GlVar],
    next: &[GlVar],
    statement_hash: &[u64; 4], // Verifier AIR's statement_hash public input
    trace_commitment: &[u64; 4],
    comp_commitment: &[u64; 4],
    fri_commitments: &[[u64; 4]], // padded to MAX_FRI_LAYERS
    params_digest: &[u64; 4],
) -> Result<Vec<GlVar>, SynthesisError> {
    const NUM_SELECTORS: usize = 3;
    const HASH_STATE_START: usize = 3;
    const HASH_STATE_WIDTH: usize = 12;
    const FRI_START: usize = 15;
    const IDX_REG: usize = 23;
    const ROOT_REG_START: usize = 24; // 4 cols
    const QGEN_CTR: usize = 28;
    const ROOT_KIND: usize = 29;
    const AUX_START: usize = 30;
    
    let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
    let zero = GlVar(FpGLVar::constant(InnerFr::from(0u64)));
    
    let mut constraints = Vec::with_capacity(34);
    
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
    //
    // Must match `src/stark/verifier_air/constraints.rs` exactly.
    for i in 0..HASH_STATE_WIDTH {
        // For Permute: verify sbox(candidate) = mid
        // This proves that candidate = inv_sbox(mid), validating the round
        let sbox_candidate = sbox_gl(cs.clone(), &candidate[i])?;
        let permute_constraint = gl_sub_light(cs.clone(), &sbox_candidate, &mid[i])?;
        
        // For Nop/Squeeze: next should equal current (copy)
        let copy_constraint = gl_sub_light(cs.clone(), &next_hash[i], &current_hash[i])?;
        
        // For Absorb: next_hash[0..3] == current_hash[0..3] and
        // next_hash[4+i] == current_hash[4+i] + absorbed[i] for i in 0..8.
        // NOTE: absorbed[0..7] are carried in fri[0..7]; Merkle index is a dedicated column (`idx_reg`).
        let absorb_constraint = if i < 4 {
            gl_sub_light(cs.clone(), &next_hash[i], &current_hash[i])?
        } else {
            let j = i - 4;
            let absorbed = &current[FRI_START + j];
            let expected = gl_add_light(cs.clone(), &current_hash[i], absorbed)?;
            gl_sub_light(cs.clone(), &next_hash[i], &expected)?
        };

        // For Init: semantics depend on aux[0] init kind in {8,9,10,11,12}.
        // See `verifier_air/constraints.rs` for the exact polynomial selectors.
        let rc = &current[AUX_START]; // aux[0]
        let k8 = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let k9 = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let k10 = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let k11 = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
        let k12 = GlVar(FpGLVar::constant(InnerFr::from(12u64)));

        // init_kind_in_range = (rc-8)(rc-9)(rc-10)(rc-11)(rc-12)
        let rc_m8 = gl_sub_light(cs.clone(), rc, &k8)?;
        let rc_m9 = gl_sub_light(cs.clone(), rc, &k9)?;
        let rc_m10 = gl_sub_light(cs.clone(), rc, &k10)?;
        let rc_m11 = gl_sub_light(cs.clone(), rc, &k11)?;
        let rc_m12 = gl_sub_light(cs.clone(), rc, &k12)?;
        let t_range = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t_range2 = gl_mul_light(cs.clone(), &t_range, &rc_m10)?;
        let t_range3 = gl_mul_light(cs.clone(), &t_range2, &rc_m11)?;
        let init_kind_in_range = gl_mul_light(cs.clone(), &t_range3, &rc_m12)?;

        // Lagrange basis over {8,9,10,11,12}:
        // denom8  = 24, denom9 = -6, denom10 = 4, denom11 = -6, denom12 = 24
        let inv24 = GlVar(FpGLVar::constant(InnerFr::from(17678129733188976641u64)));
        let inv4 = GlVar(FpGLVar::constant(InnerFr::from(13835058052060938241u64)));
        let inv_neg6 = GlVar(FpGLVar::constant(InnerFr::from(3074457344902430720u64))); // (-6)^(-1)

        // l8 = (rc-9)(rc-10)(rc-11)(rc-12)/24
        let t_l8a = gl_mul_light(cs.clone(), &rc_m9, &rc_m10)?;
        let t_l8b = gl_mul_light(cs.clone(), &t_l8a, &rc_m11)?;
        let t_l8c = gl_mul_light(cs.clone(), &t_l8b, &rc_m12)?;
        let l8 = gl_mul_light(cs.clone(), &t_l8c, &inv24)?;

        // l9 = (rc-8)(rc-10)(rc-11)(rc-12)/(-6)
        let t_l9a = gl_mul_light(cs.clone(), &rc_m8, &rc_m10)?;
        let t_l9b = gl_mul_light(cs.clone(), &t_l9a, &rc_m11)?;
        let t_l9c = gl_mul_light(cs.clone(), &t_l9b, &rc_m12)?;
        let l9 = gl_mul_light(cs.clone(), &t_l9c, &inv_neg6)?;

        // l10 = (rc-8)(rc-9)(rc-11)(rc-12)/4
        let t_l10a = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t_l10b = gl_mul_light(cs.clone(), &t_l10a, &rc_m11)?;
        let t_l10c = gl_mul_light(cs.clone(), &t_l10b, &rc_m12)?;
        let l10 = gl_mul_light(cs.clone(), &t_l10c, &inv4)?;

        // l11 = (rc-8)(rc-9)(rc-10)(rc-12)/(-6)
        let t_l11a = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t_l11b = gl_mul_light(cs.clone(), &t_l11a, &rc_m10)?;
        let t_l11c = gl_mul_light(cs.clone(), &t_l11b, &rc_m12)?;
        let l11 = gl_mul_light(cs.clone(), &t_l11c, &inv_neg6)?;

        // l12 = (rc-8)(rc-9)(rc-10)(rc-11)/24
        let t_l12a = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t_l12b = gl_mul_light(cs.clone(), &t_l12a, &rc_m10)?;
        let t_l12c = gl_mul_light(cs.clone(), &t_l12b, &rc_m11)?;
        let l12 = gl_mul_light(cs.clone(), &t_l12c, &inv24)?;

        // Kind 8: reset to zeros with state[0] = fri[0].
        let expected_reset = if i == 0 { current[FRI_START].clone() } else { zero.clone() };
        let init_reset_constraint = gl_sub_light(cs.clone(), &next_hash[i], &expected_reset)?;

        // Kind 9: load capacity[0..3] from fri[0..3], zero rest.
        let expected_load = if i < 4 { current[FRI_START + i].clone() } else { zero.clone() };
        let init_load_constraint = gl_sub_light(cs.clone(), &next_hash[i], &expected_load)?;

        // Kind 10: copy digest from rate[0..3] (hash_state[4..7]) into capacity[0..3], zero rest.
        let expected_copy = if i < 4 { current_hash[4 + i].clone() } else { zero.clone() };
        let init_copy_constraint = gl_sub_light(cs.clone(), &next_hash[i], &expected_copy)?;

        // Kind 11: Merkle merge prep with len=8.
        // dir bit is in fri[5] (0 => current left, 1 => current right).
        let dir = current[FRI_START + 5].clone();
        let one_minus_dir = gl_sub_light(cs.clone(), &one, &dir)?;
        let expected_merkle = if i == 0 {
            GlVar(FpGLVar::constant(InnerFr::from(8u64)))
        } else if i < 4 {
            zero.clone()
        } else if i < 8 {
            let j = i - 4;
            let digest_j = current_hash[j].clone();
            let sibling_j = current[FRI_START + j].clone();
            let t1 = gl_mul_light(cs.clone(), &one_minus_dir, &digest_j)?;
            let t2 = gl_mul_light(cs.clone(), &dir, &sibling_j)?;
            gl_add_light(cs.clone(), &t1, &t2)?
        } else {
            let j = i - 8;
            let digest_j = current_hash[j].clone();
            let sibling_j = current[FRI_START + j].clone();
            let t1 = gl_mul_light(cs.clone(), &one_minus_dir, &sibling_j)?;
            let t2 = gl_mul_light(cs.clone(), &dir, &digest_j)?;
            gl_add_light(cs.clone(), &t1, &t2)?
        };
        let init_merkle_constraint = gl_sub_light(cs.clone(), &next_hash[i], &expected_merkle)?;

        // Kind 12: root-load rows copy hash_state (root_reg is updated elsewhere).
        let init_rootload_constraint = gl_sub_light(cs.clone(), &next_hash[i], &current_hash[i])?;

        // init_constraint = L8*reset + L9*load + L10*copy + L11*merkle + L12*rootload
        //                + (i==0 ? init_kind_in_range : 0)
        let c8 = gl_mul_light(cs.clone(), &l8, &init_reset_constraint)?;
        let c9 = gl_mul_light(cs.clone(), &l9, &init_load_constraint)?;
        let c10 = gl_mul_light(cs.clone(), &l10, &init_copy_constraint)?;
        let c11 = gl_mul_light(cs.clone(), &l11, &init_merkle_constraint)?;
        let c89 = gl_add_light(cs.clone(), &c8, &c9)?;
        let c8910 = gl_add_light(cs.clone(), &c89, &c10)?;
        let c12 = gl_mul_light(cs.clone(), &l12, &init_rootload_constraint)?;
        let c891011 = gl_add_light(cs.clone(), &c8910, &c11)?;
        let mut init_constraint = gl_add_light(cs.clone(), &c891011, &c12)?;
        if i == 0 {
            init_constraint = gl_add_light(cs.clone(), &init_constraint, &init_kind_in_range)?;
        }
        
        // Combine constraints based on operation:
        // - Init: constrained by init_constraint
        // - Merkle/Fri/Deep/Nop: copy (state preserved)
        let term_perm = gl_mul_light(cs.clone(), &op.is_permute, &permute_constraint)?;
        let term_sq = gl_mul_light(cs.clone(), &op.is_squeeze, &copy_constraint)?;
        let term_abs = gl_mul_light(cs.clone(), &op.is_absorb, &absorb_constraint)?;
        let term_init = gl_mul_light(cs.clone(), &op.is_init, &init_constraint)?;

        let t_m1 = gl_add_light(cs.clone(), &op.is_merkle, &op.is_fri)?;
        let t_m2 = gl_add_light(cs.clone(), &t_m1, &op.is_deep)?;
        let preserve_flags = gl_add_light(cs.clone(), &t_m2, &op.is_nop)?;
        let term_preserve = gl_mul_light(cs.clone(), &preserve_flags, &copy_constraint)?;
        
        let s1 = gl_add_light(cs.clone(), &term_perm, &term_sq)?;
        let s2 = gl_add_light(cs.clone(), &s1, &term_abs)?;
        let s3 = gl_add_light(cs.clone(), &s2, &term_init)?;
        let constraint = gl_add_light(cs.clone(), &s3, &term_preserve)?;
        
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
        let t3 = gl_add_light(cs.clone(), &t2, &next_op.is_init)?;
        gl_add_light(cs.clone(), &t3, &next_op.is_absorb)?
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
    
    // Root verification constraints: hash_state[i] == root_reg[i] for i in 0..4
    let root_constraints: [GlVar; 4] = [
        gl_sub_light(cs.clone(), &current_hash[0], &current[ROOT_REG_START + 0])?,
        gl_sub_light(cs.clone(), &current_hash[1], &current[ROOT_REG_START + 1])?,
        gl_sub_light(cs.clone(), &current_hash[2], &current[ROOT_REG_START + 2])?,
        gl_sub_light(cs.clone(), &current_hash[3], &current[ROOT_REG_START + 3])?,
    ];
    
    // Statement verification constraints: hash_state[i] == pub_inputs.statement_hash[i]
    // Used when aux[2] = 4 (STATEMENT mode)
    let statement_hash_gl: [GlVar; 4] = [
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(statement_hash[0])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(statement_hash[1])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(statement_hash[2])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(statement_hash[3])))?),
    ];
    let statement_constraints: [GlVar; 4] = [
        gl_sub_light(cs.clone(), &current_hash[0], &statement_hash_gl[0])?,
        gl_sub_light(cs.clone(), &current_hash[1], &statement_hash_gl[1])?,
        gl_sub_light(cs.clone(), &current_hash[2], &statement_hash_gl[2])?,
        gl_sub_light(cs.clone(), &current_hash[3], &statement_hash_gl[3])?,
    ];
    
    // Params digest binding constraints (mode 5)
    let params_digest_gl: [GlVar; 4] = [
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(params_digest[0])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(params_digest[1])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(params_digest[2])))?),
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(params_digest[3])))?),
    ];
    let params_constraints: [GlVar; 4] = [
        gl_sub_light(cs.clone(), &current_hash[0], &params_digest_gl[0])?,
        gl_sub_light(cs.clone(), &current_hash[1], &params_digest_gl[1])?,
        gl_sub_light(cs.clone(), &current_hash[2], &params_digest_gl[2])?,
        gl_sub_light(cs.clone(), &current_hash[3], &params_digest_gl[3])?,
    ];
    
    // Root check selector: non-zero only when aux[2] = 0
    // is_root_check = Π_{k=1..6}(aux[2]-k)
    let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
    let three_gl = GlVar(FpGLVar::constant(InnerFr::from(3u64)));
    let four_gl = GlVar(FpGLVar::constant(InnerFr::from(4u64)));
    let five_gl = GlVar(FpGLVar::constant(InnerFr::from(5u64)));
    let six_gl = GlVar(FpGLVar::constant(InnerFr::from(6u64)));
    let aux_m1 = gl_sub_light(cs.clone(), aux_mode, &one)?;
    let aux_m2 = gl_sub_light(cs.clone(), aux_mode, &two_gl)?;
    let aux_m3 = gl_sub_light(cs.clone(), aux_mode, &three_gl)?;
    let aux_m4 = gl_sub_light(cs.clone(), aux_mode, &four_gl)?;
    let aux_m5 = gl_sub_light(cs.clone(), aux_mode, &five_gl)?;
    let aux_m6 = gl_sub_light(cs.clone(), aux_mode, &six_gl)?;
    let is_root_check_temp = gl_mul_light(cs.clone(), &aux_m1, &aux_m2)?;
    let is_root_check_temp2 = gl_mul_light(cs.clone(), &is_root_check_temp, &aux_m3)?;
    let is_root_check_temp3 = gl_mul_light(cs.clone(), &is_root_check_temp2, &aux_m4)?;
    let is_root_check_temp4 = gl_mul_light(cs.clone(), &is_root_check_temp3, &aux_m5)?;
    let is_root_check = gl_mul_light(cs.clone(), &is_root_check_temp4, &aux_m6)?;
    
    // Statement check for mode 4
    // is_statement_check = aux[2] * (aux[2]-1) * (aux[2]-2) * (aux[2]-3) * (aux[2]-5) * (aux[2]-6)
    // When aux[2] = 4: 4*3*2*1*(-1) = -24 (non-zero, check applies)
    // When aux[2] = 0,1,2,3,5: is_statement_check = 0 (check doesn't apply)
    let is_statement_check_temp = gl_mul_light(cs.clone(), aux_mode, &aux_m1)?;
    let is_statement_check_temp2 = gl_mul_light(cs.clone(), &is_statement_check_temp, &aux_m2)?;
    let is_statement_check_temp3 = gl_mul_light(cs.clone(), &is_statement_check_temp2, &aux_m3)?;
    let is_statement_check_temp4 = gl_mul_light(cs.clone(), &is_statement_check_temp3, &aux_m5)?;
    let is_statement_check = gl_mul_light(cs.clone(), &is_statement_check_temp4, &aux_m6)?;
    
    // is_params_check = aux[2] * (aux[2]-1) * (aux[2]-2) * (aux[2]-3) * (aux[2]-4) * (aux[2]-6)
    let is_params_check_temp = gl_mul_light(cs.clone(), aux_mode, &aux_m1)?;
    let is_params_check_temp2 = gl_mul_light(cs.clone(), &is_params_check_temp, &aux_m2)?;
    let is_params_check_temp3 = gl_mul_light(cs.clone(), &is_params_check_temp2, &aux_m3)?;
    let is_params_check_temp4 = gl_mul_light(cs.clone(), &is_params_check_temp3, &aux_m4)?;
    let is_params_check = gl_mul_light(cs.clone(), &is_params_check_temp4, &aux_m6)?;

    // ========================================================================
    // NOP SUB-MODE SELECTORS (computed once per row)
    //
    // Mirrors `src/stark/verifier_air/constraints.rs`:
    // Allowed Nop sub-modes: {0,6,8,9,10,11,12,13}.
    // Use Lagrange basis over points {0,6,7,8,9,10,11,12,13}.
    // NOTE: we keep the interpolation set (including 7) even though 7 is disallowed by the
    // aux[2] range constraint; this avoids re-deriving constants.
    // ========================================================================
    let seven_gl = GlVar(FpGLVar::constant(InnerFr::from(7u64)));
    let eight_gl = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
    let nine_gl = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
    let ten_gl = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
    let eleven_gl = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
    let twelve_gl = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
    let thirteen_gl = GlVar(FpGLVar::constant(InnerFr::from(13u64)));

    // Denominator inverses for Lagrange basis over {0,6,7,8,9,10,11,12,13}.
    let inv_neg_30240 = GlVar(FpGLVar::constant(InnerFr::from(4978302855505701807u64)));
    let inv_neg_1920 = GlVar(FpGLVar::constant(InnerFr::from(9607679202820096u64)));
    let inv_1296 = GlVar(FpGLVar::constant(InnerFr::from(12966808524102381417u64)));
    let inv_neg_1440 = GlVar(FpGLVar::constant(InnerFr::from(12310639618546816342u64)));
    let inv_2640 = GlVar(FpGLVar::constant(InnerFr::from(13408826465608555800u64)));
    let inv_neg_8640 = GlVar(FpGLVar::constant(InnerFr::from(8200687959562664164u64)));
    let inv_65520 = GlVar(FpGLVar::constant(InnerFr::from(540282385061150600u64)));

    let aux_m7 = gl_sub_light(cs.clone(), aux_mode, &seven_gl)?;
    let aux_m8 = gl_sub_light(cs.clone(), aux_mode, &eight_gl)?;
    let aux_m9 = gl_sub_light(cs.clone(), aux_mode, &nine_gl)?;
    let aux_m10 = gl_sub_light(cs.clone(), aux_mode, &ten_gl)?;
    let aux_m11 = gl_sub_light(cs.clone(), aux_mode, &eleven_gl)?;
    let aux_m12 = gl_sub_light(cs.clone(), aux_mode, &twelve_gl)?;
    let aux_m13 = gl_sub_light(cs.clone(), aux_mode, &thirteen_gl)?;

    // is_qgen: mode 6 (denom = -30240)
    let q1 = gl_mul_light(cs.clone(), aux_mode, &aux_m7)?;
    let q2 = gl_mul_light(cs.clone(), &q1, &aux_m8)?;
    let q3 = gl_mul_light(cs.clone(), &q2, &aux_m9)?;
    let q4 = gl_mul_light(cs.clone(), &q3, &aux_m10)?;
    let q5 = gl_mul_light(cs.clone(), &q4, &aux_m11)?;
    let q6 = gl_mul_light(cs.clone(), &q5, &aux_m12)?;
    let q7 = gl_mul_light(cs.clone(), &q6, &aux_m13)?;
    let is_qgen = gl_mul_light(cs.clone(), &q7, &inv_neg_30240)?;

    // is_zerocheck: mode 8 (denom = -1920)
    let z1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let z2 = gl_mul_light(cs.clone(), &z1, &aux_m7)?;
    let z3 = gl_mul_light(cs.clone(), &z2, &aux_m9)?;
    let z4 = gl_mul_light(cs.clone(), &z3, &aux_m10)?;
    let z5 = gl_mul_light(cs.clone(), &z4, &aux_m11)?;
    let z6 = gl_mul_light(cs.clone(), &z5, &aux_m12)?;
    let z7 = gl_mul_light(cs.clone(), &z6, &aux_m13)?;
    let is_zerocheck = gl_mul_light(cs.clone(), &z7, &inv_neg_1920)?;

    // is_canon: mode 9 (denom = 1296)
    let c1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let c2 = gl_mul_light(cs.clone(), &c1, &aux_m7)?;
    let c3 = gl_mul_light(cs.clone(), &c2, &aux_m8)?;
    let c4 = gl_mul_light(cs.clone(), &c3, &aux_m10)?;
    let c5 = gl_mul_light(cs.clone(), &c4, &aux_m11)?;
    let c6 = gl_mul_light(cs.clone(), &c5, &aux_m12)?;
    let c7 = gl_mul_light(cs.clone(), &c6, &aux_m13)?;
    let is_canon = gl_mul_light(cs.clone(), &c7, &inv_1296)?;

    // is_powshift: mode 10 (denom = -1440)
    let p1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let p2 = gl_mul_light(cs.clone(), &p1, &aux_m7)?;
    let p3 = gl_mul_light(cs.clone(), &p2, &aux_m8)?;
    let p4 = gl_mul_light(cs.clone(), &p3, &aux_m9)?;
    let p5 = gl_mul_light(cs.clone(), &p4, &aux_m11)?;
    let p6 = gl_mul_light(cs.clone(), &p5, &aux_m12)?;
    let p7 = gl_mul_light(cs.clone(), &p6, &aux_m13)?;
    let is_powshift = gl_mul_light(cs.clone(), &p7, &inv_neg_1440)?;

    // is_capture: mode 11 (denom = 2640)
    let k1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let k2 = gl_mul_light(cs.clone(), &k1, &aux_m7)?;
    let k3 = gl_mul_light(cs.clone(), &k2, &aux_m8)?;
    let k4 = gl_mul_light(cs.clone(), &k3, &aux_m9)?;
    let k5 = gl_mul_light(cs.clone(), &k4, &aux_m10)?;
    let k6 = gl_mul_light(cs.clone(), &k5, &aux_m12)?;
    let k7 = gl_mul_light(cs.clone(), &k6, &aux_m13)?;
    let is_capture = gl_mul_light(cs.clone(), &k7, &inv_2640)?;

    // is_export: mode 12 (denom = -8640)
    let e1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let e2 = gl_mul_light(cs.clone(), &e1, &aux_m7)?;
    let e3 = gl_mul_light(cs.clone(), &e2, &aux_m8)?;
    let e4 = gl_mul_light(cs.clone(), &e3, &aux_m9)?;
    let e5 = gl_mul_light(cs.clone(), &e4, &aux_m10)?;
    let e6 = gl_mul_light(cs.clone(), &e5, &aux_m11)?;
    let e7 = gl_mul_light(cs.clone(), &e6, &aux_m13)?;
    let is_export = gl_mul_light(cs.clone(), &e7, &inv_neg_8640)?;

    // is_freeze: mode 13 (denom = 65520)
    let f1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
    let f2 = gl_mul_light(cs.clone(), &f1, &aux_m7)?;
    let f3 = gl_mul_light(cs.clone(), &f2, &aux_m8)?;
    let f4 = gl_mul_light(cs.clone(), &f3, &aux_m9)?;
    let f5 = gl_mul_light(cs.clone(), &f4, &aux_m10)?;
    let f6 = gl_mul_light(cs.clone(), &f5, &aux_m11)?;
    let f7 = gl_mul_light(cs.clone(), &f6, &aux_m12)?;
    let is_freeze = gl_mul_light(cs.clone(), &f7, &inv_65520)?;

    let is_qgen_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_qgen)?;
    let is_zerocheck_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_zerocheck)?;
    let is_canon_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_canon)?;
    let is_powshift_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_powshift)?;
    let is_capture_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_capture)?;
    let is_export_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_export)?;
    let is_freeze_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_freeze)?;

    // Default "special nop" set for copy gating on most columns.
    let t1 = gl_add_light(cs.clone(), &is_qgen_nop, &is_zerocheck_nop)?;
    let t2 = gl_add_light(cs.clone(), &t1, &is_canon_nop)?;
    let t3 = gl_add_light(cs.clone(), &t2, &is_powshift_nop)?;
    let t4 = gl_add_light(cs.clone(), &t3, &is_capture_nop)?;
    let t5 = gl_add_light(cs.clone(), &t4, &is_export_nop)?;
    let t_q = gl_add_light(cs.clone(), &t5, &is_freeze_nop)?;
    let one_minus_q = gl_sub_light(cs.clone(), &one, &t_q)?;
    let copy_ok = gl_mul_light(cs.clone(), &both_not_special, &one_minus_q)?;
    
    for i in 0..8 {
        let fri_curr = &current[FRI_START + i];
        let fri_next = &next[FRI_START + i];
        let copy_constraint = gl_sub_light(cs.clone(), fri_next, fri_curr)?;
        
        if i == 4 {
            // FRI column 4: FRI folding result
            // During FriFold: verify folding formula is correct
            // Also enforce copy on non-special transitions (column 4 is used as scratch elsewhere).
            let fold_term = gl_mul_light(cs.clone(), &op.is_fri, &fri_fold_constraint)?;
            // Copy gating for column 4 matches AIR: do NOT disable copy on capture/canon rows,
            // but do disable on shift/export rows.
            let t4a = gl_add_light(cs.clone(), &is_qgen_nop, &is_zerocheck_nop)?;
            let t4b = gl_add_light(cs.clone(), &t4a, &is_powshift_nop)?;
            let t4c = gl_add_light(cs.clone(), &t4b, &is_export_nop)?;
            let t_q4 = gl_add_light(cs.clone(), &t4c, &is_freeze_nop)?;
            let one_minus_q4 = gl_sub_light(cs.clone(), &one, &t_q4)?;
            let copy_ok4 = gl_mul_light(cs.clone(), &both_not_special, &one_minus_q4)?;
            let copy_term = gl_mul_light(cs.clone(), &copy_ok4, &copy_constraint)?;
            // QueryGen / PoWShift shift: fri4_cur = 2*fri4_next + fri5_cur.
            let bit = current[FRI_START + 5].clone();
            let two_idx_next = gl_mul_light(cs.clone(), &two_gl, fri_next)?;
            let rhs_qgen = gl_add_light(cs.clone(), &two_idx_next, &bit)?;
            let qgen_shift = gl_sub_light(cs.clone(), fri_curr, &rhs_qgen)?;
            let qp = gl_add_light(cs.clone(), &is_qgen_nop, &is_powshift_nop)?;
            let qgen_sel = gl_add_light(cs.clone(), &qp, &is_freeze_nop)?;
            let qgen_term = gl_mul_light(cs.clone(), &qgen_sel, &qgen_shift)?;

            // ZeroCheck on Nop rows with aux[2]=8: enforce fri[4] == 0.
            let zero_term = gl_mul_light(cs.clone(), &is_zerocheck_nop, fri_curr)?;

            // Capture on Nop rows with aux[2]=11: enforce fri[4] == hash_state[0].
            let capture_constraint = gl_sub_light(cs.clone(), fri_curr, &current_hash[0])?;
            let capture_term = gl_mul_light(cs.clone(), &is_capture_nop, &capture_constraint)?;

            // Canonicality on Nop rows with aux[2]=9:
            // enforce hi32 != (2^32-1) by requiring an inverse witness:
            //   (hi32 - (2^32-1)) * w = 1
            // where hi32 = fri[4], w = fri[5].
            let all_ones_32 = GlVar(FpGLVar::constant(InnerFr::from(0xFFFF_FFFFu64)));
            let hi32 = fri_curr.clone();
            let w = current[FRI_START + 5].clone();
            let hi_m = gl_sub_light(cs.clone(), &hi32, &all_ones_32)?;
            let lhs = gl_mul_light(cs.clone(), &hi_m, &w)?;
            let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
            let canon_eq = gl_sub_light(cs.clone(), &lhs, &one_gl)?;
            let canon_term = gl_mul_light(cs.clone(), &is_canon_nop, &canon_eq)?;

            let fc = gl_add_light(cs.clone(), &fold_term, &copy_term)?;
            let fcq = gl_add_light(cs.clone(), &fc, &qgen_term)?;
            let fcqdz = gl_add_light(cs.clone(), &fcq, &zero_term)?;
            let fcqdzc = gl_add_light(cs.clone(), &fcqdz, &capture_term)?;
            constraints.push(gl_add_light(cs.clone(), &fcqdzc, &canon_term)?);
        } else if i == 6 {
            // FRI column 6: equality verification on ALL DeepCompose rows.
            let ood_term = gl_mul_light(cs.clone(), &op.is_deep, &equality_constraint)?;

            // Copy gating for column 6 matches AIR:
            // disable copy only on rows that *update* the accumulator (qgen / powshift).
            let t6a = gl_add_light(cs.clone(), &is_qgen_nop, &is_powshift_nop)?;
            let one_minus_q6 = gl_sub_light(cs.clone(), &one, &t6a)?;
            let copy_ok6 = gl_mul_light(cs.clone(), &both_not_special, &one_minus_q6)?;
            let copy_term = gl_mul_light(cs.clone(), &copy_ok6, &copy_constraint)?;

            // QueryGen accumulator update: acc_next = acc_cur + bit * pow2.
            let bit = current[FRI_START + 5].clone();
            let pow2 = current[FRI_START + 7].clone();
            let bit_pow2 = gl_mul_light(cs.clone(), &bit, &pow2)?;
            let rhs = gl_add_light(cs.clone(), fri_curr, &bit_pow2)?;
            let acc_update = gl_sub_light(cs.clone(), fri_next, &rhs)?;
            let qgen_sel = gl_add_light(cs.clone(), &is_qgen_nop, &is_powshift_nop)?;
            let qgen_term = gl_mul_light(cs.clone(), &qgen_sel, &acc_update)?;

            // Freeze: acc_next == acc_cur
            let acc_copy = gl_sub_light(cs.clone(), fri_next, fri_curr)?;
            let freeze_term = gl_mul_light(cs.clone(), &is_freeze_nop, &acc_copy)?;
            // Capture: acc == 0
            let capture_acc_zero = gl_mul_light(cs.clone(), &is_capture_nop, fri_curr)?;

            let t = gl_add_light(cs.clone(), &ood_term, &copy_term)?;
            let t = gl_add_light(cs.clone(), &t, &qgen_term)?;
            let t = gl_add_light(cs.clone(), &t, &freeze_term)?;
            let t = gl_add_light(cs.clone(), &t, &capture_acc_zero)?;
            constraints.push(t);
            // (the rest of the column-6 accumulator constraints were integrated above)
        } else if i < 4 {
            // FRI columns 0-3: ROOT/STATEMENT/PARAMS VERIFICATION
            //
            // ROOT mode (aux[2] = 0): verify hash_state[i] == fri[i]
            // STATEMENT mode (aux[2] = 4): verify hash_state[i] == pub_inputs.statement_hash[i]
            // PARAMS mode (aux[2] = 5): verify hash_state[i] == params digest
            //
            // is_root_check = Π_{k=1..6}(aux[2]-k) = non-zero when aux[2]=0
            // is_statement_check = aux[2](aux[2]-1)(aux[2]-2)(aux[2]-3)(aux[2]-5)(aux[2]-6) = non-zero when aux[2]=4
            // is_params_check = aux[2](aux[2]-1)(aux[2]-2)(aux[2]-3)(aux[2]-4)(aux[2]-6) = non-zero when aux[2]=5
            //
            // Constraint: op.is_deep * is_root_check * root_constraint
            //           + op.is_deep * is_statement_check * statement_constraint
            //           + both_not_special * copy_constraint = 0
            let deep_root = gl_mul_light(cs.clone(), &op.is_deep, &is_root_check)?;
            let root_term = gl_mul_light(cs.clone(), &deep_root, &root_constraints[i])?;
            
            // Statement hash verification for mode 4
            let deep_statement = gl_mul_light(cs.clone(), &op.is_deep, &is_statement_check)?;
            let statement_term = gl_mul_light(cs.clone(), &deep_statement, &statement_constraints[i])?;
            
            // Params digest verification for mode 5
            let deep_params = gl_mul_light(cs.clone(), &op.is_deep, &is_params_check)?;
            let params_term = gl_mul_light(cs.clone(), &deep_params, &params_constraints[i])?;
            
            let copy_term = gl_mul_light(cs.clone(), &both_not_special, &copy_constraint)?;
            
            // Full constraint: root term + statement term + params term + copy term
            let c1 = gl_add_light(cs.clone(), &root_term, &statement_term)?;
            let c2 = gl_add_light(cs.clone(), &c1, &params_term)?;
            let c = gl_add_light(cs.clone(), &c2, &copy_term)?;
            constraints.push(c);
        } else {
            // FRI columns 5, 7: copy constraint only
            if i == 5 {
                // For Init kind 11, enforce dir bit in fri[5] is binary.
                let rc = &current[AUX_START];
                let k8 = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
                let k9 = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
                let k10 = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
                let k12 = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
                let inv_neg6 = GlVar(FpGLVar::constant(InnerFr::from(3074457344902430720u64))); // (-6)^(-1)
                let rc_m8 = gl_sub_light(cs.clone(), rc, &k8)?;
                let rc_m9 = gl_sub_light(cs.clone(), rc, &k9)?;
                let rc_m10 = gl_sub_light(cs.clone(), rc, &k10)?;
                let rc_m12 = gl_sub_light(cs.clone(), rc, &k12)?;
                let t_l11a = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
                let t_l11b = gl_mul_light(cs.clone(), &t_l11a, &rc_m10)?;
                let t_l11c = gl_mul_light(cs.clone(), &t_l11b, &rc_m12)?;
                let l11 = gl_mul_light(cs.clone(), &t_l11c, &inv_neg6)?;

                let dir = fri_curr;
                // enforce_binary: dir * (dir - 1)
                let dir_m1 = gl_sub_light(cs.clone(), dir, &one)?;
                let bin = gl_mul_light(cs.clone(), dir, &dir_m1)?;
                let init_l11 = gl_mul_light(cs.clone(), &op.is_init, &l11)?;
                let bin_term = gl_mul_light(cs.clone(), &init_l11, &bin)?;

                let copy_term = gl_mul_light(cs.clone(), &copy_ok, &copy_constraint)?;
                // QueryGen/PoWShift bit must be binary on aux[2]=6/10 Nop rows.
                let bit = fri_curr;
                let bit_m1 = gl_sub_light(cs.clone(), bit, &one)?;
                let qgen_bin = gl_mul_light(cs.clone(), bit, &bit_m1)?;
                // In AIR, the binary constraint is applied only in QueryGen mode (aux[2]=6).
                let qgen_term = gl_mul_light(cs.clone(), &is_qgen_nop, &qgen_bin)?;
                // PoWShift: enforce bit == 0.
                let pow_bit_zero = gl_mul_light(cs.clone(), &is_powshift_nop, bit)?;
                // Freeze: bit must be binary.
                let freeze_bin = gl_mul_light(cs.clone(), &is_freeze_nop, &qgen_bin)?;
                let t = gl_add_light(cs.clone(), &copy_term, &bin_term)?;
                let t2 = gl_add_light(cs.clone(), &t, &qgen_term)?;
                let t3 = gl_add_light(cs.clone(), &t2, &pow_bit_zero)?;
                constraints.push(gl_add_light(cs.clone(), &t3, &freeze_bin)?);
            } else {
                // i == 7: QueryGen pow2 update: pow2_next = 2*pow2_cur.
                // Copy gating for column 7 matches AIR: do NOT disable copy on capture rows.
                let t7a = gl_add_light(cs.clone(), &is_qgen_nop, &is_zerocheck_nop)?;
                let t7b = gl_add_light(cs.clone(), &t7a, &is_canon_nop)?;
                let t7c = gl_add_light(cs.clone(), &t7b, &is_powshift_nop)?;
                let t7d = gl_add_light(cs.clone(), &t7c, &is_export_nop)?;
                let one_minus_q7 = gl_sub_light(cs.clone(), &one, &t7d)?;
                let copy_ok7 = gl_mul_light(cs.clone(), &both_not_special, &one_minus_q7)?;
                let copy_term = gl_mul_light(cs.clone(), &copy_ok7, &copy_constraint)?;
                let two_pow2 = gl_mul_light(cs.clone(), &two_gl, fri_curr)?;
                let pow2_update = gl_sub_light(cs.clone(), fri_next, &two_pow2)?;
                let qgen_sel = gl_add_light(cs.clone(), &is_qgen_nop, &is_powshift_nop)?;
                let qgen_term = gl_mul_light(cs.clone(), &qgen_sel, &pow2_update)?;
                // Capture: pow2 == 1
                let pow2_m1 = gl_sub_light(cs.clone(), fri_curr, &one)?;
                let capture_pow2_one = gl_mul_light(cs.clone(), &is_capture_nop, &pow2_m1)?;
                let t = gl_add_light(cs.clone(), &copy_term, &qgen_term)?;
                constraints.push(gl_add_light(cs.clone(), &t, &capture_pow2_one)?);
            }
        }
    }
    
    // --- 8. Index register constraint (1) ---
    //
    // Mirrors `verifier_air/constraints.rs` IDX_REG:
    // - default copy
    // - Init kind 11: idx_cur = 2*idx_next + dir (dir in fri[5])
    // - DeepCompose root-check (aux[2]=0): idx == 0
    // - Export Nop (aux[2]=12): idx_next == fri[6]
    {
        let idx_curr = &current[IDX_REG];
        let idx_next = &next[IDX_REG];
        let copy_constraint = gl_sub_light(cs.clone(), idx_next, idx_curr)?;

        // l11 selector for init kind 11 over {8,9,10,11,12}:
        // l11 = (rc-8)(rc-9)(rc-10)(rc-12)/(-6)
        let rc = &current[AUX_START]; // aux[0]
        let k8 = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let k9 = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let k10 = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let k12 = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
        let inv_neg6 = GlVar(FpGLVar::constant(InnerFr::from(3074457344902430720u64))); // (-6)^(-1)
        let rc_m8 = gl_sub_light(cs.clone(), rc, &k8)?;
        let rc_m9 = gl_sub_light(cs.clone(), rc, &k9)?;
        let rc_m10 = gl_sub_light(cs.clone(), rc, &k10)?;
        let rc_m12 = gl_sub_light(cs.clone(), rc, &k12)?;
        let t_l11a = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t_l11b = gl_mul_light(cs.clone(), &t_l11a, &rc_m10)?;
        let t_l11c = gl_mul_light(cs.clone(), &t_l11b, &rc_m12)?;
        let l11 = gl_mul_light(cs.clone(), &t_l11c, &inv_neg6)?;

        let dir = current[FRI_START + 5].clone();
        let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
        let two_idx_next = gl_mul_light(cs.clone(), &two_gl, idx_next)?;
        let rhs = gl_add_light(cs.clone(), &two_idx_next, &dir)?;
        let idx_update_constraint = gl_sub_light(cs.clone(), idx_curr, &rhs)?;
        let init_l11 = gl_mul_light(cs.clone(), &op.is_init, &l11)?;
        let merkle_idx_update = gl_mul_light(cs.clone(), &init_l11, &idx_update_constraint)?;

        // Root-mode idx must be consumed: op.is_deep * is_root_check * idx == 0.
        let deep_root = gl_mul_light(cs.clone(), &op.is_deep, &is_root_check)?;
        let root_idx_zero = gl_mul_light(cs.clone(), &deep_root, idx_curr)?;


        // Export selector (aux[2]=12) (Lagrange over {0,6,7,8,9,10,11,12,13}).
        let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
        let six_gl = GlVar(FpGLVar::constant(InnerFr::from(6u64)));
        let seven_gl = GlVar(FpGLVar::constant(InnerFr::from(7u64)));
        let eight_gl = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let nine_gl = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let ten_gl = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let eleven_gl = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
        let twelve_gl = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
        let thirteen_gl = GlVar(FpGLVar::constant(InnerFr::from(13u64)));
        let inv_neg_8640 = GlVar(FpGLVar::constant(InnerFr::from(8200687959562664164u64)));
        let inv_neg_1920 = GlVar(FpGLVar::constant(InnerFr::from(9607679202820096u64)));
        let aux_m6 = gl_sub_light(cs.clone(), aux_mode, &six_gl)?;
        let aux_m7 = gl_sub_light(cs.clone(), aux_mode, &seven_gl)?;
        let aux_m8 = gl_sub_light(cs.clone(), aux_mode, &eight_gl)?;
        let aux_m9 = gl_sub_light(cs.clone(), aux_mode, &nine_gl)?;
        let aux_m10 = gl_sub_light(cs.clone(), aux_mode, &ten_gl)?;
        let aux_m11 = gl_sub_light(cs.clone(), aux_mode, &eleven_gl)?;
        let aux_m12 = gl_sub_light(cs.clone(), aux_mode, &twelve_gl)?;
        let aux_m13 = gl_sub_light(cs.clone(), aux_mode, &thirteen_gl)?;
        // is_export: mode 12 (denom = -8640)
        let e1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
        let e2 = gl_mul_light(cs.clone(), &e1, &aux_m7)?;
        let e3 = gl_mul_light(cs.clone(), &e2, &aux_m8)?;
        let e4 = gl_mul_light(cs.clone(), &e3, &aux_m9)?;
        let e5 = gl_mul_light(cs.clone(), &e4, &aux_m10)?;
        let e6 = gl_mul_light(cs.clone(), &e5, &aux_m11)?;
        let e7 = gl_mul_light(cs.clone(), &e6, &aux_m13)?;
        let is_export = gl_mul_light(cs.clone(), &e7, &inv_neg_8640)?;
        let is_export_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_export)?;

        // Enforce: if next row is export_nop, current row must be zerocheck_nop.
        let next_mode = &next[AUX_START + 2];
        let nm_m6 = gl_sub_light(cs.clone(), next_mode, &six_gl)?;
        let nm_m7 = gl_sub_light(cs.clone(), next_mode, &seven_gl)?;
        let nm_m8 = gl_sub_light(cs.clone(), next_mode, &eight_gl)?;
        let nm_m9 = gl_sub_light(cs.clone(), next_mode, &nine_gl)?;
        let nm_m10 = gl_sub_light(cs.clone(), next_mode, &ten_gl)?;
        let nm_m11 = gl_sub_light(cs.clone(), next_mode, &eleven_gl)?;
        let nm_m13 = gl_sub_light(cs.clone(), next_mode, &thirteen_gl)?;
        // next_is_export: mode 12 (denom = -8640) over {0,6,7,8,9,10,11,12,13}
        let ne1 = gl_mul_light(cs.clone(), next_mode, &nm_m6)?;
        let ne2 = gl_mul_light(cs.clone(), &ne1, &nm_m7)?;
        let ne3 = gl_mul_light(cs.clone(), &ne2, &nm_m8)?;
        let ne4 = gl_mul_light(cs.clone(), &ne3, &nm_m9)?;
        let ne5 = gl_mul_light(cs.clone(), &ne4, &nm_m10)?;
        let ne6 = gl_mul_light(cs.clone(), &ne5, &nm_m11)?;
        let ne7 = gl_mul_light(cs.clone(), &ne6, &nm_m13)?;
        let next_is_export = gl_mul_light(cs.clone(), &ne7, &inv_neg_8640)?;
        let next_is_export_nop = gl_mul_light(cs.clone(), &next_op.is_nop, &next_is_export)?;

        // current_is_zerocheck: mode 8 (denom = -1920) over {0,6,7,8,9,10,11,12,13}
        // is_zerocheck = mode*(mode-6)*(mode-7)*(mode-9)*(mode-10)*(mode-11)*(mode-12)*(mode-13) * inv(-1920)
        let z1 = gl_mul_light(cs.clone(), aux_mode, &aux_m6)?;
        let z2 = gl_mul_light(cs.clone(), &z1, &aux_m7)?;
        let z3 = gl_mul_light(cs.clone(), &z2, &aux_m9)?;
        let z4 = gl_mul_light(cs.clone(), &z3, &aux_m10)?;
        let z5 = gl_mul_light(cs.clone(), &z4, &aux_m11)?;
        let z6 = gl_mul_light(cs.clone(), &z5, &aux_m12)?;
        let z7 = gl_mul_light(cs.clone(), &z6, &aux_m13)?;
        let is_zerocheck = gl_mul_light(cs.clone(), &z7, &inv_neg_1920)?;
        let is_zerocheck_nop = gl_mul_light(cs.clone(), &op.is_nop, &is_zerocheck)?;

        let one_minus_zerocheck = gl_sub_light(cs.clone(), &one, &is_zerocheck_nop)?;
        let export_requires_prev_zerocheck = gl_mul_light(cs.clone(), &next_is_export_nop, &one_minus_zerocheck)?;

        let export_constraint = gl_sub_light(cs.clone(), idx_next, &current[FRI_START + 6])?;
        let export_term = gl_mul_light(cs.clone(), &is_export_nop, &export_constraint)?;

        let init_term = gl_mul_light(cs.clone(), &op.is_init, &l11)?;
        let copy_ok = gl_sub_light(cs.clone(), &one, &init_term)?;
        let copy_ok = gl_sub_light(cs.clone(), &copy_ok, &is_export_nop)?;
        let copy_term = gl_mul_light(cs.clone(), &copy_ok, &copy_constraint)?;

        let t = gl_add_light(cs.clone(), &copy_term, &merkle_idx_update)?;
        let t2 = gl_add_light(cs.clone(), &t, &root_idx_zero)?;
        let t3 = gl_add_light(cs.clone(), &t2, &export_term)?;
        constraints.push(gl_add_light(cs.clone(), &t3, &export_requires_prev_zerocheck)?);
    }

    // --- 9. QueryGen step counter constraints (1) ---
    //
    // Mirrors `verifier_air/constraints.rs` qgen_ctr:
    // - capture (aux[2]=11): next = 0
    // - qgen/powshift/freeze (aux[2] in {6,10,13}): next = cur + 1
    // - otherwise: copy (except allow reset on transitions INTO capture)
    // - export rows require ctr==64 and the row immediately before an export also requires ctr==64
    {
        let ctr_cur = &current[QGEN_CTR];
        let ctr_next = &next[QGEN_CTR];

        let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
        let sixty_four = GlVar(FpGLVar::constant(InnerFr::from(64u64)));

        let copy = gl_sub_light(cs.clone(), ctr_next, ctr_cur)?;
        let cur_plus_one = gl_add_light(cs.clone(), ctr_cur, &one_gl)?;
        let inc = gl_sub_light(cs.clone(), ctr_next, &cur_plus_one)?;
        let reset = ctr_next.clone(); // == 0

        let qp = gl_add_light(cs.clone(), &is_qgen_nop, &is_powshift_nop)?;
        let inc_mode = gl_add_light(cs.clone(), &qp, &is_freeze_nop)?;

        // other_mode = 1 - is_capture_nop - inc_mode
        let t = gl_add_light(cs.clone(), &is_capture_nop, &inc_mode)?;
        let other_mode = gl_sub_light(cs.clone(), &one_gl, &t)?;

        // export requires ctr==64
        let ctr_minus_64 = gl_sub_light(cs.clone(), ctr_cur, &sixty_four)?;
        let export_requires_ctr = gl_mul_light(cs.clone(), &is_export_nop, &ctr_minus_64)?;

        // prev_export requires ctr==64: if next row is export_nop, enforce ctr_cur==64
        let next_mode = &next[AUX_START + 2];
        let six_gl = GlVar(FpGLVar::constant(InnerFr::from(6u64)));
        let seven_gl = GlVar(FpGLVar::constant(InnerFr::from(7u64)));
        let eight_gl = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let nine_gl = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let ten_gl = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let eleven_gl = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
        let twelve_gl = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
        let thirteen_gl = GlVar(FpGLVar::constant(InnerFr::from(13u64)));
        let inv_neg_8640 = GlVar(FpGLVar::constant(InnerFr::from(8200687959562664164u64)));
        let inv_2640 = GlVar(FpGLVar::constant(InnerFr::from(13408826465608555800u64)));

        let nm_m6 = gl_sub_light(cs.clone(), next_mode, &six_gl)?;
        let nm_m7 = gl_sub_light(cs.clone(), next_mode, &seven_gl)?;
        let nm_m8 = gl_sub_light(cs.clone(), next_mode, &eight_gl)?;
        let nm_m9 = gl_sub_light(cs.clone(), next_mode, &nine_gl)?;
        let nm_m10 = gl_sub_light(cs.clone(), next_mode, &ten_gl)?;
        let nm_m11 = gl_sub_light(cs.clone(), next_mode, &eleven_gl)?;
        let nm_m12 = gl_sub_light(cs.clone(), next_mode, &twelve_gl)?;
        let nm_m13 = gl_sub_light(cs.clone(), next_mode, &thirteen_gl)?;

        // next_is_export: mode 12 (denom = -8640) over {0,6,7,8,9,10,11,12,13}
        let ne1 = gl_mul_light(cs.clone(), next_mode, &nm_m6)?;
        let ne2 = gl_mul_light(cs.clone(), &ne1, &nm_m7)?;
        let ne3 = gl_mul_light(cs.clone(), &ne2, &nm_m8)?;
        let ne4 = gl_mul_light(cs.clone(), &ne3, &nm_m9)?;
        let ne5 = gl_mul_light(cs.clone(), &ne4, &nm_m10)?;
        let ne6 = gl_mul_light(cs.clone(), &ne5, &nm_m11)?;
        let ne7 = gl_mul_light(cs.clone(), &ne6, &nm_m13)?;
        let next_is_export = gl_mul_light(cs.clone(), &ne7, &inv_neg_8640)?;
        let next_is_export_nop = gl_mul_light(cs.clone(), &next_op.is_nop, &next_is_export)?;
        let prev_export_requires_ctr = gl_mul_light(cs.clone(), &next_is_export_nop, &ctr_minus_64)?;

        // Allow reset at the start of microprogram: disable copy on transitions INTO capture.
        // next_is_capture: mode 11 (denom = 2640) over {0,6,7,8,9,10,11,12,13}
        let nc1 = gl_mul_light(cs.clone(), next_mode, &nm_m6)?;
        let nc2 = gl_mul_light(cs.clone(), &nc1, &nm_m7)?;
        let nc3 = gl_mul_light(cs.clone(), &nc2, &nm_m8)?;
        let nc4 = gl_mul_light(cs.clone(), &nc3, &nm_m9)?;
        let nc5 = gl_mul_light(cs.clone(), &nc4, &nm_m10)?;
        let nc6 = gl_mul_light(cs.clone(), &nc5, &nm_m12)?;
        let nc7 = gl_mul_light(cs.clone(), &nc6, &nm_m13)?;
        let next_is_capture = gl_mul_light(cs.clone(), &nc7, &inv_2640)?;
        let next_is_capture_nop = gl_mul_light(cs.clone(), &next_op.is_nop, &next_is_capture)?;
        let one_minus_next_capture = gl_sub_light(cs.clone(), &one_gl, &next_is_capture_nop)?;

        let copy_if_ok = gl_mul_light(cs.clone(), &one_minus_next_capture, &copy)?;
        let copy_term = gl_mul_light(cs.clone(), &other_mode, &copy_if_ok)?;
        let reset_term = gl_mul_light(cs.clone(), &is_capture_nop, &reset)?;
        let inc_term = gl_mul_light(cs.clone(), &inc_mode, &inc)?;

        let t1 = gl_add_light(cs.clone(), &reset_term, &inc_term)?;
        let t2 = gl_add_light(cs.clone(), &t1, &copy_term)?;
        let t3 = gl_add_light(cs.clone(), &t2, &export_requires_ctr)?;
        constraints.push(gl_add_light(cs.clone(), &t3, &prev_export_requires_ctr)?);
    }

    // --- 10. Expected-root register constraints (4) ---
    //
    // Mirrors `verifier_air/constraints.rs` root_reg binding on LOAD_ROOT4 (init-kind 12):
    // - default copy
    // - update on LOAD_ROOT4: root_next[j] = fri_curr[j]
    // - bind loaded fri[0..3] to the public-input commitment selected by `root_kind`
    {
        use winter_math::fields::f64::BaseElement as GlBase;
        use winter_math::FieldElement;

        let trace_commitment_gl: [GlVar; 4] = [
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(trace_commitment[0])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(trace_commitment[1])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(trace_commitment[2])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(trace_commitment[3])))?),
        ];
        let comp_commitment_gl: [GlVar; 4] = [
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(comp_commitment[0])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(comp_commitment[1])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(comp_commitment[2])))?),
            GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(comp_commitment[3])))?),
        ];

        const MAX_FRI_LAYERS: usize = 32;
        if fri_commitments.len() < MAX_FRI_LAYERS {
            return Err(SynthesisError::Unsatisfiable);
        }
        let mut fri_roots_gl: Vec<[GlVar; 4]> = Vec::with_capacity(MAX_FRI_LAYERS);
        for i in 0..MAX_FRI_LAYERS {
            let c = fri_commitments[i];
            fri_roots_gl.push([
                GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c[0])))?),
                GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c[1])))?),
                GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c[2])))?),
                GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c[3])))?),
            ]);
        }

        // Lagrange selector for init kind 12 over {8,9,10,11,12}: l12 = (rc-8)(rc-9)(rc-10)(rc-11)/24
        let rc = &current[AUX_START]; // aux[0]
        let k8 = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let k9 = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let k10 = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let k11 = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
        let inv24 = GlVar(FpGLVar::constant(InnerFr::from(17678129733188976641u64)));
        let rc_m8 = gl_sub_light(cs.clone(), rc, &k8)?;
        let rc_m9 = gl_sub_light(cs.clone(), rc, &k9)?;
        let rc_m10 = gl_sub_light(cs.clone(), rc, &k10)?;
        let rc_m11 = gl_sub_light(cs.clone(), rc, &k11)?;
        let t = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t2 = gl_mul_light(cs.clone(), &t, &rc_m10)?;
        let num = gl_mul_light(cs.clone(), &t2, &rc_m11)?;
        let l12 = gl_mul_light(cs.clone(), &num, &inv24)?;
        let is_load_root = gl_mul_light(cs.clone(), &op.is_init, &l12)?;

        let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
        let copy_ok = gl_sub_light(cs.clone(), &one, &is_load_root)?;

        // root_kind selection
        let rk = &current[ROOT_KIND];
        let max_kind = 1 + MAX_FRI_LAYERS; // 17

        // rk_range = Π_{k=0..max_kind} (rk - k)  (implemented as rk * Π_{k=1..max_kind} (rk - k))
        let mut rk_range = rk.clone();
        for k in 1..=(max_kind as u64) {
            let k_gl = GlVar(FpGLVar::constant(InnerFr::from(k)));
            let rk_mk = gl_sub_light(cs.clone(), rk, &k_gl)?;
            rk_range = gl_mul_light(cs.clone(), &rk_range, &rk_mk)?;
        }

        // sels[k] = L_k(rk) over points {0..=max_kind}
        let mut sels: Vec<GlVar> = Vec::with_capacity(max_kind + 1);
        for k in 0..=max_kind {
            let mut num_k = one.clone();
            for m in 0..=max_kind {
                if m == k {
                    continue;
                }
                let m_gl = GlVar(FpGLVar::constant(InnerFr::from(m as u64)));
                let rk_mm = gl_sub_light(cs.clone(), rk, &m_gl)?;
                num_k = gl_mul_light(cs.clone(), &num_k, &rk_mm)?;
            }
            // denom = Π_{m!=k} (k - m) in Goldilocks; invert in Goldilocks and embed as u64 constant.
            let mut den = GlBase::ONE;
            let k_fe = GlBase::new(k as u64);
            for m in 0..=max_kind {
                if m == k {
                    continue;
                }
                let m_fe = GlBase::new(m as u64);
                den *= k_fe - m_fe;
            }
            let den_inv_u64 = den.inv().as_int();
            let den_inv = GlVar(FpGLVar::constant(InnerFr::from(den_inv_u64)));
            sels.push(gl_mul_light(cs.clone(), &num_k, &den_inv)?);
        }

        for j in 0..4 {
            let root_curr = &current[ROOT_REG_START + j];
            let root_next = &next[ROOT_REG_START + j];
            let copy_constraint = gl_sub_light(cs.clone(), root_next, root_curr)?;
            let update_constraint = gl_sub_light(cs.clone(), root_next, &current[FRI_START + j])?;

            // expected = sel0*trace + sel1*comp + Σ sel_{2+i}*fri[i]
            let t0 = gl_mul_light(cs.clone(), &sels[0], &trace_commitment_gl[j])?;
            let t1 = gl_mul_light(cs.clone(), &sels[1], &comp_commitment_gl[j])?;
            let mut expected = gl_add_light(cs.clone(), &t0, &t1)?;
            for i in 0..MAX_FRI_LAYERS {
                let sel = &sels[2 + i];
                let term = gl_mul_light(cs.clone(), sel, &fri_roots_gl[i][j])?;
                expected = gl_add_light(cs.clone(), &expected, &term)?;
            }
            let bind_loaded = gl_sub_light(cs.clone(), &current[FRI_START + j], &expected)?;

            let copy_term = gl_mul_light(cs.clone(), &copy_ok, &copy_constraint)?;
            let update_term = gl_mul_light(cs.clone(), &is_load_root, &update_constraint)?;
            let bind_term = gl_mul_light(cs.clone(), &is_load_root, &bind_loaded)?;
            let mut c = gl_add_light(cs.clone(), &copy_term, &update_term)?;
            c = gl_add_light(cs.clone(), &c, &bind_term)?;
            if j == 0 {
                // enforce rk_range == 0 on load_root rows
                let rk_term = gl_mul_light(cs.clone(), &is_load_root, &rk_range)?;
                c = gl_add_light(cs.clone(), &c, &rk_term)?;
            }
            constraints.push(c);
        }
    }

    // --- 11. Root-kind selector constraints (1) ---
    //
    // Mirrors `verifier_air/constraints.rs` root_kind:
    // allow root_kind to change only on transitions INTO Init(kind=LOAD_ROOT4) rows.
    {
        let rk_cur = &current[ROOT_KIND];
        let rk_next = &next[ROOT_KIND];
        let copy_constraint = gl_sub_light(cs.clone(), rk_next, rk_cur)?;

        // Allow updates when the NEXT row is Init(kind=LOAD_ROOT4).
        let next_rc = &next[AUX_START]; // aux[0] on next row
        let k8 = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
        let k9 = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
        let k10 = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
        let k11 = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
        let inv24 = GlVar(FpGLVar::constant(InnerFr::from(17678129733188976641u64)));
        let rc_m8 = gl_sub_light(cs.clone(), next_rc, &k8)?;
        let rc_m9 = gl_sub_light(cs.clone(), next_rc, &k9)?;
        let rc_m10 = gl_sub_light(cs.clone(), next_rc, &k10)?;
        let rc_m11 = gl_sub_light(cs.clone(), next_rc, &k11)?;
        let t = gl_mul_light(cs.clone(), &rc_m8, &rc_m9)?;
        let t2 = gl_mul_light(cs.clone(), &t, &rc_m10)?;
        let num = gl_mul_light(cs.clone(), &t2, &rc_m11)?;
        let l12_next = gl_mul_light(cs.clone(), &num, &inv24)?;
        let next_is_load_root = gl_mul_light(cs.clone(), &next_op.is_init, &l12_next)?;
        let one = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
        let copy_ok = gl_sub_light(cs.clone(), &one, &next_is_load_root)?;
        constraints.push(gl_mul_light(cs.clone(), &copy_ok, &copy_constraint)?);
    }

    // --- 12. Auxiliary constraints (4) ---
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
        } else if i == 1 {
            // Mode counter
            //
            // Tracks:
            // - root checks (mode 0): +2^32 per root check
            // - statement hash (mode 4): +1
            // - params digest (mode 5): +4096
            //
            // Packed encoding:
            //   aux[1] = statement_count
            //          + 4096 * params_count
            //          + 65536 * fri_link_count
            //          + 2^32 * root_count
            //
            // Update rules:
            // - On DeepCompose mode 0: aux[1] += 2^32
            // - On DeepCompose mode 4: aux[1] += 1
            // - On DeepCompose mode 5: aux[1] += 4096
            // - On DeepCompose mode 3: aux[1] += 65536
            // - Otherwise: aux[1] unchanged
            //
            // Constraint: aux[1]_next - aux[1]_curr - is_deep * (is_mode_0 * 2^32 + is_mode_4 + is_mode_5 * 4096) = 0
            //
            // We compute is_mode_4 / is_mode_5 and normalize them to 0/1
            let mode = aux_mode;
            let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
            let three_gl = GlVar(FpGLVar::constant(InnerFr::from(3u64)));
            let four_gl = GlVar(FpGLVar::constant(InnerFr::from(4u64)));
            let five_gl = GlVar(FpGLVar::constant(InnerFr::from(5u64)));
            let four_thousand_ninety_six = GlVar(FpGLVar::constant(InnerFr::from(4096u64)));
            let two_pow_32 = GlVar(FpGLVar::constant(InnerFr::from(1u64 << 32)));
            
            // Compute mode selectors (reusing what we have)
            let mode_m1 = gl_sub_light(cs.clone(), mode, &one)?;
            let mode_m2 = gl_sub_light(cs.clone(), mode, &two_gl)?;
            let mode_m3 = gl_sub_light(cs.clone(), mode, &three_gl)?;
            let mode_m4 = gl_sub_light(cs.clone(), mode, &four_gl)?;
            let mode_m5 = gl_sub_light(cs.clone(), mode, &five_gl)?;
            
            // is_mode_4_raw = mode * (mode-1) * (mode-2) * (mode-3) * (mode-5) * (mode-6) = 48 when mode=4
            let p1 = gl_mul_light(cs.clone(), mode, &mode_m1)?;
            let p2 = gl_mul_light(cs.clone(), &p1, &mode_m2)?;
            let p3 = gl_mul_light(cs.clone(), &p2, &mode_m3)?;
            let p4 = gl_mul_light(cs.clone(), &p3, &mode_m5)?;
            let is_mode_4_raw = gl_mul_light(cs.clone(), &p4, &aux_m6)?;
            // Normalize: divide by 48 (multiply by inverse)
            // 48^(-1) mod Goldilocks prime = 18062436901301780481
            let inv_48 = GlVar(FpGLVar::constant(InnerFr::from(18062436901301780481u64)));
            let is_mode_4 = gl_mul_light(cs.clone(), &is_mode_4_raw, &inv_48)?;
            
            // is_mode_5_raw = mode * (mode-1) * (mode-2) * (mode-3) * (mode-4) * (mode-6) = -120 when mode=5
            let q1 = gl_mul_light(cs.clone(), mode, &mode_m1)?;
            let q2 = gl_mul_light(cs.clone(), &q1, &mode_m2)?;
            let q3 = gl_mul_light(cs.clone(), &q2, &mode_m3)?;
            let q4 = gl_mul_light(cs.clone(), &q3, &mode_m4)?;
            let is_mode_5_raw = gl_mul_light(cs.clone(), &q4, &aux_m6)?;
            // Normalize: divide by -120 (multiply by inverse)
            // (-120)^(-1) mod Goldilocks prime = 153722867245121536
            let inv_neg_120 = GlVar(FpGLVar::constant(InnerFr::from(153722867245121536u64)));
            let is_mode_5 = gl_mul_light(cs.clone(), &is_mode_5_raw, &inv_neg_120)?;

            // is_mode_0_raw = (mode-1)(mode-2)(mode-3)(mode-4)(mode-5) = -120 when mode=0
            let r1 = gl_mul_light(cs.clone(), &mode_m1, &mode_m2)?;
            let r2 = gl_mul_light(cs.clone(), &r1, &mode_m3)?;
            let r3 = gl_mul_light(cs.clone(), &r2, &mode_m4)?;
            let is_mode_0_raw = gl_mul_light(cs.clone(), &r3, &mode_m5)?;
            let is_mode_0 = gl_mul_light(cs.clone(), &is_mode_0_raw, &inv_neg_120)?;

            // is_mode_3_raw = mode*(mode-1)*(mode-2)*(mode-4)*(mode-5) = 12 when mode=3
            let s1 = gl_mul_light(cs.clone(), mode, &mode_m1)?;
            let s2 = gl_mul_light(cs.clone(), &s1, &mode_m2)?;
            let s3 = gl_mul_light(cs.clone(), &s2, &mode_m4)?;
            let is_mode_3_raw = gl_mul_light(cs.clone(), &s3, &mode_m5)?;
            // Normalize by 12
            let inv_12 = GlVar(FpGLVar::constant(InnerFr::from(13835058052060938241u64))); // 12^{-1} in Goldilocks
            let is_mode_3 = gl_mul_light(cs.clone(), &is_mode_3_raw, &inv_12)?;
            
            // increment = is_mode_0 * 2^32 + is_mode_4 + is_mode_5 * 4096 + is_mode_3 * 65536
            let mode_5_scaled = gl_mul_light(cs.clone(), &is_mode_5, &four_thousand_ninety_six)?;
            let mode_0_scaled = gl_mul_light(cs.clone(), &is_mode_0, &two_pow_32)?;
            let sixty_five_thousand_five_hundred_thirty_six = GlVar(FpGLVar::constant(InnerFr::from(65536u64)));
            let mode_3_scaled = gl_mul_light(cs.clone(), &is_mode_3, &sixty_five_thousand_five_hundred_thirty_six)?;
            let t_inc = gl_add_light(cs.clone(), &mode_0_scaled, &is_mode_4)?;
            let t_inc2 = gl_add_light(cs.clone(), &t_inc, &mode_5_scaled)?;
            let mode_increment = gl_add_light(cs.clone(), &t_inc2, &mode_3_scaled)?;
            
            // final_increment = is_deep * mode_increment
            let final_increment = gl_mul_light(cs.clone(), &op.is_deep, &mode_increment)?;
            
            // Constraint: aux[1]_next - aux[1]_curr - final_increment = 0
            let diff = gl_sub_light(cs.clone(), aux_next, aux_curr)?;
            let c = gl_sub_light(cs.clone(), &diff, &final_increment)?;
            constraints.push(c);
        } else if i == 3 {
            // Checkpoint counter
            // 
            // This counter MUST increment by exactly 1 on each DeepCompose operation.
            // The boundary constraint then ensures the final count equals expected.
            // This prevents attackers from skipping verification steps.
            //
            // Constraint: aux_next - aux_curr - is_deep = 0
            let checkpoint_constraint = gl_sub_light(cs.clone(), aux_next, aux_curr)?;
            let c = gl_sub_light(cs.clone(), &checkpoint_constraint, &op.is_deep)?;
            constraints.push(c);
        } else {
            // aux[2]: mode value.
            //
            // SECURITY:
            // - On Nop rows, restrict aux[2] to {0,6,8,9,10,11,12,13} to keep sub-mode selectors well-defined.
            // - On DeepCompose rows, restrict aux[2] to {0,1,2,3,4,5} to prevent skippable checks.
            let mode = aux_curr;
            let six = GlVar(FpGLVar::constant(InnerFr::from(6u64)));
            let eight = GlVar(FpGLVar::constant(InnerFr::from(8u64)));
            let nine = GlVar(FpGLVar::constant(InnerFr::from(9u64)));
            let ten = GlVar(FpGLVar::constant(InnerFr::from(10u64)));
            let eleven = GlVar(FpGLVar::constant(InnerFr::from(11u64)));
            let twelve = GlVar(FpGLVar::constant(InnerFr::from(12u64)));
            let thirteen = GlVar(FpGLVar::constant(InnerFr::from(13u64)));
            let m6 = gl_sub_light(cs.clone(), mode, &six)?;
            let t = gl_mul_light(cs.clone(), mode, &m6)?;
            let m8 = gl_sub_light(cs.clone(), mode, &eight)?;
            let t3 = gl_mul_light(cs.clone(), &t, &m8)?;
            let m9 = gl_sub_light(cs.clone(), mode, &nine)?;
            let t4 = gl_mul_light(cs.clone(), &t3, &m9)?;
            let m10 = gl_sub_light(cs.clone(), mode, &ten)?;
            let t5 = gl_mul_light(cs.clone(), &t4, &m10)?;
            let m11 = gl_sub_light(cs.clone(), mode, &eleven)?;
            let t6 = gl_mul_light(cs.clone(), &t5, &m11)?;
            let m12 = gl_sub_light(cs.clone(), mode, &twelve)?;
            let t7 = gl_mul_light(cs.clone(), &t6, &m12)?;
            let m13 = gl_sub_light(cs.clone(), mode, &thirteen)?;
            let in_set = gl_mul_light(cs.clone(), &t7, &m13)?;

            // DeepCompose allowed set {0,1,2,3,4,5}: mode*(mode-1)*(mode-2)*(mode-3)*(mode-4)*(mode-5)=0
            let two_gl = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
            let three_gl = GlVar(FpGLVar::constant(InnerFr::from(3u64)));
            let four_gl = GlVar(FpGLVar::constant(InnerFr::from(4u64)));
            let five_gl = GlVar(FpGLVar::constant(InnerFr::from(5u64)));
            let dm1 = gl_sub_light(cs.clone(), mode, &one)?;
            let dm2 = gl_sub_light(cs.clone(), mode, &two_gl)?;
            let dm3 = gl_sub_light(cs.clone(), mode, &three_gl)?;
            let dm4 = gl_sub_light(cs.clone(), mode, &four_gl)?;
            let dm5 = gl_sub_light(cs.clone(), mode, &five_gl)?;
            let p01 = gl_mul_light(cs.clone(), mode, &dm1)?;
            let p012 = gl_mul_light(cs.clone(), &p01, &dm2)?;
            let p0123 = gl_mul_light(cs.clone(), &p012, &dm3)?;
            let p01234 = gl_mul_light(cs.clone(), &p0123, &dm4)?;
            let deep_in_set = gl_mul_light(cs.clone(), &p01234, &dm5)?;

            let nop_term = gl_mul_light(cs.clone(), &op.is_nop, &in_set)?;
            let deep_term = gl_mul_light(cs.clone(), &op.is_deep, &deep_in_set)?;
            constraints.push(gl_add_light(cs.clone(), &nop_term, &deep_term)?);
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

// ============================================================================
// CONSISTENCY TESTS (AIR vs R1CS evaluator)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::test_utils::{build_vdf_recursive_stark_instance, build_vdf_recursive_stark_instance_with_fri};
    use crate::stark::verifier_air::constraints as air_constraints;
    use crate::stark::verifier_air::VerifierPublicInputs;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use winter_math::fields::f64::BaseElement as GL;
    use winter_math::FieldElement as _;
    use winterfell::EvaluationFrame;

    fn parse_verifier_pub_inputs_from_u64s(stark_pub_inputs: &[u64]) -> VerifierPublicInputs {
        // Must match `VerifierPublicInputs::to_elements()`:
        // [stmt(4)][trace(4)][comp(4)][fri(4*k, k>=1 padded)][num_queries][proof_trace_len][g_trace][pub_result]
        // [expected_checkpoint_count][expected_mode_counter][params_digest(4)]
        assert!(stark_pub_inputs.len() >= 24);
        let n = stark_pub_inputs.len();
        let tail10_start = n - 10;
        let fri_start = 12;
        assert!(tail10_start >= fri_start);
        assert!((tail10_start - fri_start) % 4 == 0);
        let fri_len = (tail10_start - fri_start) / 4;
        let mut fri_commitments = Vec::with_capacity(fri_len);
        for i in 0..fri_len {
            let off = fri_start + 4 * i;
            fri_commitments.push([
                GL::new(stark_pub_inputs[off]),
                GL::new(stark_pub_inputs[off + 1]),
                GL::new(stark_pub_inputs[off + 2]),
                GL::new(stark_pub_inputs[off + 3]),
            ]);
        }

        VerifierPublicInputs {
            statement_hash: [
                GL::new(stark_pub_inputs[0]),
                GL::new(stark_pub_inputs[1]),
                GL::new(stark_pub_inputs[2]),
                GL::new(stark_pub_inputs[3]),
            ],
            trace_commitment: [
                GL::new(stark_pub_inputs[4]),
                GL::new(stark_pub_inputs[5]),
                GL::new(stark_pub_inputs[6]),
                GL::new(stark_pub_inputs[7]),
            ],
            comp_commitment: [
                GL::new(stark_pub_inputs[8]),
                GL::new(stark_pub_inputs[9]),
                GL::new(stark_pub_inputs[10]),
                GL::new(stark_pub_inputs[11]),
            ],
            fri_commitments,
            num_queries: stark_pub_inputs[n - 10] as usize,
            proof_trace_len: stark_pub_inputs[n - 9] as usize,
            g_trace: GL::new(stark_pub_inputs[n - 8]),
            pub_result: GL::new(stark_pub_inputs[n - 7]),
            expected_checkpoint_count: stark_pub_inputs[n - 6] as usize,
            expected_mode_counter: stark_pub_inputs[n - 5] as usize,
            params_digest: [
                GL::new(stark_pub_inputs[n - 4]),
                GL::new(stark_pub_inputs[n - 3]),
                GL::new(stark_pub_inputs[n - 2]),
                GL::new(stark_pub_inputs[n - 1]),
            ],
        }
    }

    #[test]
    fn test_r1cs_transition_eval_matches_air_on_real_ood_frame() {
        const N: usize = 34;
        // Build a real VerifierAir proof instance and reuse its parsed OOD frame rows.
        let instance = build_vdf_recursive_stark_instance(3, 8);
        let circuit = instance.circuit;

        let pub_inputs = parse_verifier_pub_inputs_from_u64s(&circuit.stark_pub_inputs);
        let statement_hash_u64: [u64; 4] = pub_inputs.statement_hash.map(|x| x.as_int());
        let params_digest_u64: [u64; 4] = pub_inputs.params_digest.map(|x| x.as_int());

        // AIR evaluation on the OOD frame rows (as field elements).
        let cur_be: Vec<GL> = circuit.ood_trace_current.iter().map(|&u| GL::new(u)).collect();
        let nxt_be: Vec<GL> = circuit.ood_trace_next.iter().map(|&u| GL::new(u)).collect();
        assert_eq!(cur_be.len(), N);
        assert_eq!(nxt_be.len(), N);

        let frame = EvaluationFrame::from_rows(cur_be.clone(), nxt_be.clone());
        let periodic_values: Vec<GL> = vec![];
        let mut air_out = vec![GL::ZERO; N];
        air_constraints::evaluate_all(&frame, &periodic_values, &mut air_out, &pub_inputs);

        // R1CS evaluator: allocate the same rows as witnesses and compare evaluated values.
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        let mut cur_gl = Vec::with_capacity(N);
        let mut nxt_gl = Vec::with_capacity(N);
        for i in 0..N {
            let u_cur = circuit.ood_trace_current[i];
            let u_nxt = circuit.ood_trace_next[i];
            cur_gl.push(GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(u_cur))).unwrap()));
            nxt_gl.push(GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(u_nxt))).unwrap()));
        }

        let trace_commitment_u64: [u64; 4] = pub_inputs.trace_commitment.map(|x| x.as_int());
        let comp_commitment_u64: [u64; 4] = pub_inputs.comp_commitment.map(|x| x.as_int());
        const MAX_FRI_LAYERS: usize = 32;
        let mut fri_commitments_u64: Vec<[u64; 4]> = Vec::with_capacity(MAX_FRI_LAYERS);
        for i in 0..MAX_FRI_LAYERS {
            let c = pub_inputs
                .fri_commitments
                .get(i)
                .copied()
                .unwrap_or([GL::ZERO; 4]);
            fri_commitments_u64.push(c.map(|x| x.as_int()));
        }

        let r1cs_vals = super::evaluate_verifier_air_constraints_gl(
            cs.clone(),
            &cur_gl,
            &nxt_gl,
            &statement_hash_u64,
            &trace_commitment_u64,
            &comp_commitment_u64,
            &fri_commitments_u64,
            &params_digest_u64,
        )
        .unwrap();
        assert_eq!(r1cs_vals.len(), N);

        for i in 0..N {
            let expected = air_out[i].as_int();
            let got = r1cs_vals[i].0.value().unwrap();
            assert_eq!(
                got,
                InnerFr::from(expected),
                "constraint {} mismatch: expected {} got {:?}",
                i,
                expected,
                got
            );
        }
    }

    #[test]
    fn test_r1cs_transition_eval_matches_air_on_real_ood_frame_with_fri() {
        const N: usize = 34;
        // Build a real VerifierAir proof instance which includes non-trivial FRI layers.
        let instance = build_vdf_recursive_stark_instance_with_fri(3, 8);
        let circuit = instance.circuit;

        let pub_inputs = parse_verifier_pub_inputs_from_u64s(&circuit.stark_pub_inputs);
        let statement_hash_u64: [u64; 4] = pub_inputs.statement_hash.map(|x| x.as_int());
        let params_digest_u64: [u64; 4] = pub_inputs.params_digest.map(|x| x.as_int());

        let cur_be: Vec<GL> = circuit.ood_trace_current.iter().map(|&u| GL::new(u)).collect();
        let nxt_be: Vec<GL> = circuit.ood_trace_next.iter().map(|&u| GL::new(u)).collect();
        assert_eq!(cur_be.len(), N);
        assert_eq!(nxt_be.len(), N);

        let frame = EvaluationFrame::from_rows(cur_be.clone(), nxt_be.clone());
        let periodic_values: Vec<GL> = vec![];
        let mut air_out = vec![GL::ZERO; N];
        air_constraints::evaluate_all(&frame, &periodic_values, &mut air_out, &pub_inputs);

        let cs = ConstraintSystem::<InnerFr>::new_ref();
        let mut cur_gl = Vec::with_capacity(N);
        let mut nxt_gl = Vec::with_capacity(N);
        for i in 0..N {
            let u_cur = circuit.ood_trace_current[i];
            let u_nxt = circuit.ood_trace_next[i];
            cur_gl.push(GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(u_cur))).unwrap()));
            nxt_gl.push(GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(u_nxt))).unwrap()));
        }

        let trace_commitment_u64: [u64; 4] = pub_inputs.trace_commitment.map(|x| x.as_int());
        let comp_commitment_u64: [u64; 4] = pub_inputs.comp_commitment.map(|x| x.as_int());
        const MAX_FRI_LAYERS: usize = 32;
        let mut fri_commitments_u64: Vec<[u64; 4]> = Vec::with_capacity(MAX_FRI_LAYERS);
        for i in 0..MAX_FRI_LAYERS {
            let c = pub_inputs
                .fri_commitments
                .get(i)
                .copied()
                .unwrap_or([GL::ZERO; 4]);
            fri_commitments_u64.push(c.map(|x| x.as_int()));
        }

        let r1cs_vals = super::evaluate_verifier_air_constraints_gl(
            cs.clone(),
            &cur_gl,
            &nxt_gl,
            &statement_hash_u64,
            &trace_commitment_u64,
            &comp_commitment_u64,
            &fri_commitments_u64,
            &params_digest_u64,
        )
        .unwrap();
        assert_eq!(r1cs_vals.len(), N);

        for i in 0..N {
            let expected = air_out[i].as_int();
            let got = r1cs_vals[i].0.value().unwrap();
            assert_eq!(
                got,
                InnerFr::from(expected),
                "constraint {} mismatch (with FRI): expected {} got {:?}",
                i,
                expected,
                got
            );
        }
    }
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
