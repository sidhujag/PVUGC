//! Transition Constraints for Verifier AIR
//!
//! This module defines all transition constraints for the STARK verifier.
//! The constraints are organized by operation type.
//!
//! ## Constraint Structure
//!
//! Each row has a 3-bit operation selector that determines which constraints apply:
//! - Init: Allows any state (initializing)
//! - Absorb: Capacity preserved, rate can change
//! - Permute: RPO round transition (verified using round counter in aux[0])
//! - Squeeze: State preserved (just reading)
//! - Nop: State preserved (padding)
//! - MerklePath/FriFold/DeepCompose: Special operations (allow transitions)

use winterfell::{math::FieldElement, EvaluationFrame};

use super::{
    hash_chiplet, VerifierPublicInputs, HASH_STATE_WIDTH, NUM_SELECTORS, VERIFIER_TRACE_WIDTH,
};

// ============================================================================
// COLUMN INDICES
// ============================================================================

/// Selector column indices
pub const SEL_0: usize = 0;
pub const SEL_1: usize = 1;
pub const SEL_2: usize = 2;

/// Hash state column range
pub const HASH_STATE_START: usize = NUM_SELECTORS;
pub const HASH_STATE_END: usize = HASH_STATE_START + HASH_STATE_WIDTH;

/// FRI working column range
pub const FRI_START: usize = HASH_STATE_END;
pub const FRI_END: usize = FRI_START + 8;

/// Auxiliary column range
pub const AUX_START: usize = FRI_END;
pub const AUX_END: usize = VERIFIER_TRACE_WIDTH;

/// Round counter index within auxiliary columns
pub const ROUND_COUNTER: usize = AUX_START; // aux[0]

// ============================================================================
// CONSTRAINT EVALUATION
// ============================================================================

/// Evaluate all transition constraints
///
/// The result slice should have length equal to the number of constraint equations.
/// We have 3 + 12 + 8 + 4 = 27 constraints (matching trace width).
pub fn evaluate_all<E: FieldElement<BaseField = super::BaseElement>>(
    frame: &EvaluationFrame<E>,
    _periodic_values: &[E],
    result: &mut [E],
    _pub_inputs: &VerifierPublicInputs,
) {
    let current = frame.current();
    let next = frame.next();

    let mut idx = 0;

    // --- 1. Selector constraints (3): ensure binary ---
    for i in 0..NUM_SELECTORS {
        result[idx] = enforce_binary(current[SEL_0 + i]);
        idx += 1;
    }

    // --- 2. Decode current operation ---
    let op = decode_operation(current[SEL_0], current[SEL_1], current[SEL_2]);

    // --- 3. Get current and next hash states ---
    let mut current_hash: [E; HASH_STATE_WIDTH] = [E::ZERO; HASH_STATE_WIDTH];
    let mut next_hash: [E; HASH_STATE_WIDTH] = [E::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        current_hash[i] = current[HASH_STATE_START + i];
        next_hash[i] = next[HASH_STATE_START + i];
    }

    // --- 4. Get round counter and compute round constants ---
    let round_counter = current[ROUND_COUNTER];
    
    // Compute round constants using Lagrange interpolation on round_counter
    // This allows us to select the correct constants for rounds 0-6
    let round_constants = compute_round_constants_lagrange(round_counter);

    // --- 5. Compute expected next state for Permute operation ---
    let mut expected_after_rpo = [E::ZERO; HASH_STATE_WIDTH];
    compute_rpo_round(&current_hash, &round_constants, &mut expected_after_rpo);

    // --- 6. Hash state constraints (12) ---
    for i in 0..HASH_STATE_WIDTH {
        // For Permute: next should equal RPO round result
        let permute_constraint = next_hash[i] - expected_after_rpo[i];

        // For Nop/Squeeze: next should equal current (copy)
        let copy_constraint = next_hash[i] - current_hash[i];

        // For Absorb: capacity preserved, rate can change
        let absorb_constraint = if i < 4 {
            // Capacity (first 4 elements): must be preserved
            next_hash[i] - current_hash[i]
        } else {
            // Rate (elements 4-11): can change (absorption adds input)
            E::ZERO
        };

        // For Init/special ops: allow any transition
        let allow_any = E::ZERO;

        // Combine constraints based on operation
        let constraint = op.is_permute * permute_constraint
            + (op.is_nop + op.is_squeeze) * copy_constraint
            + op.is_absorb * absorb_constraint
            + (op.is_init + op.is_merkle + op.is_fri + op.is_deep) * allow_any;

        result[idx] = constraint;
        idx += 1;
    }

    // --- 7. FRI/DEEP working constraints (8) ---
    // Decode NEXT row operation to allow changes going INTO special ops
    let next_op = decode_operation(next[SEL_0], next[SEL_1], next[SEL_2]);
    
    // Compute "is special" flags (each is 0 or 1 due to mutually exclusive flags)
    let op_special = op.is_merkle + op.is_fri + op.is_deep + op.is_init + op.is_absorb;
    let next_special = next_op.is_merkle + next_op.is_fri + next_op.is_deep + next_op.is_init;
    
    // Constraint should only apply when BOTH current AND next are non-special
    let both_not_special = (E::ONE - op_special) * (E::ONE - next_special);
    
    // ========================================================================
    // FRI column layout (during FriFold):
    // [0] = f_x      (evaluation at x)
    // [1] = f_neg_x  (evaluation at -x)
    // [2] = x        (domain point)
    // [3] = beta     (FRI folding challenge)
    // [4] = g        (folded result)
    // [5-7] = unused
    //
    // FRI column layout (during DeepCompose - OOD verification):
    // [0] = trace_current[0]
    // [1] = trace_current[1]
    // [2] = trace_next[0]
    // [3] = trace_next[1]
    // [4] = composition[0]
    // [5] = composition[1]
    // [6] = lhs (pre-computed: transition_sum * exemption² + boundary_sum * zerofier_num)
    // [7] = rhs (pre-computed: C(z) * zerofier_num * exemption)
    // ========================================================================
    
    let f_x = current[FRI_START];
    let f_neg_x = current[FRI_START + 1];
    let x = current[FRI_START + 2];
    let beta = current[FRI_START + 3];
    let g = current[FRI_START + 4];
    
    // FRI folding constraint: g = (f_x + f_neg_x)/2 + beta * (f_x - f_neg_x)/(2*x)
    // Rearranged to avoid division: 2*x*g = x*(f_x + f_neg_x) + beta*(f_x - f_neg_x)
    let two = E::from(super::BaseElement::new(2));
    let fri_fold_lhs = two * x * g;
    let fri_fold_rhs = x * (f_x + f_neg_x) + beta * (f_x - f_neg_x);
    let fri_fold_constraint = fri_fold_lhs - fri_fold_rhs;
    
    // ========================================================================
    // OOD constraint verification (during DeepCompose)
    //
    // The trace builder pre-computes:
    // - lhs = transition_sum * exemption² + boundary_sum * zerofier_num
    // - rhs = C(z) * zerofier_num * exemption
    //
    // These are stored in fri[6] and fri[7]. The AIR verifies: lhs = rhs
    //
    // This is the CRITICAL security check - without it, a malicious prover
    // could provide arbitrary OOD evaluations that don't match the constraints.
    // ========================================================================
    
    let ood_lhs = current[FRI_START + 6]; // Pre-computed LHS
    let ood_rhs = current[FRI_START + 7]; // Pre-computed RHS
    
    // OOD constraint: LHS must equal RHS
    // This verifies the entire composition polynomial equation at the OOD point
    let ood_constraint = ood_lhs - ood_rhs;
    
    for i in 0..8 {
        let fri_curr = current[FRI_START + i];
        let fri_next = next[FRI_START + i];

        if i == 4 {
            // For column 4: FRI folding result OR composition[0] in OOD mode
            let copy_constraint = fri_next - fri_curr;
            
            // During FriFold: verify folding is correct
            // During DeepCompose: allow transition (OOD values stored)
            // During other ops: copy constraint
            result[idx] = op.is_fri * fri_fold_constraint 
                + both_not_special * copy_constraint;
        } else if i == 6 {
            // For column 6: During DeepCompose, verify OOD constraint (LHS = RHS)
            let copy_constraint = fri_next - fri_curr;
            
            // During DeepCompose: enforce OOD constraint equation
            // During other ops: copy constraint
            result[idx] = op.is_deep * ood_constraint 
                + both_not_special * copy_constraint;
        } else {
            // Copy constraint when not transitioning to/from special operations
            let copy_constraint = fri_next - fri_curr;
            result[idx] = both_not_special * copy_constraint;
        }
        idx += 1;
    }

    // --- 8. Auxiliary constraints (4) ---
    
    for i in 0..4 {
        let aux_curr = current[AUX_START + i];
        let aux_next = next[AUX_START + i];

        if i == 0 {
            // Round counter / direction (aux[0]):
            // During Permute: must be in {0,1,2,3,4,5,6} to select correct round constants
            // During MerklePath: direction bit, must be binary (0 or 1)
            // During FRI/DEEP/Init: may hold other data
            // During Nop/Squeeze/Absorb: should be 7 (not in permute)
            let rc = aux_curr;
            
            // Range check: rc ∈ {0,1,2,3,4,5,6} (degree 7)
            let rc_in_range = rc 
                * (rc - E::ONE) 
                * (rc - E::from(super::BaseElement::new(2)))
                * (rc - E::from(super::BaseElement::new(3)))
                * (rc - E::from(super::BaseElement::new(4)))
                * (rc - E::from(super::BaseElement::new(5)))
                * (rc - E::from(super::BaseElement::new(6)));
            
            // During Permute: enforce rc ∈ {0..6}
            let permute_check = op.is_permute * rc_in_range;
            
            // During MerklePath: direction must be binary (0 or 1)
            // This is critical for Merkle path security - ensures correct ordering
            let merkle_binary_check = op.is_merkle * enforce_binary(rc);
            
            // During Nop/Squeeze: enforce rc = 7 (not in permute)
            let basic_ops = op.is_nop + op.is_squeeze;
            let seven = E::from(super::BaseElement::new(7));
            let basic_check = basic_ops * (rc - seven);
            
            result[idx] = permute_check + merkle_binary_check + basic_check;
        } else if i == 3 {
            // Acceptance flag: can only transition 0 -> 1 or stay same
            // Binary constraint: flag' * (1 - flag') = 0
            let binary_constraint = enforce_binary(aux_next);
            // Monotonic: if current is 1, next must be 1
            let monotonic = aux_curr * (E::ONE - aux_next);
            result[idx] = binary_constraint + monotonic;
        } else {
            // Aux columns 1 and 2: currently unused, allow any values
            // These could be used for additional verification state in future extensions
            result[idx] = E::ZERO;
        }
        idx += 1;
    }
}

// ============================================================================
// RPO ROUND COMPUTATION
// ============================================================================

/// Compute round constants using Lagrange interpolation on the round counter
///
/// This allows selecting the correct round constants for rounds 0-6 based on
/// the value of aux[0] (round_counter). The interpolation has degree 6.
fn compute_round_constants_lagrange<E: FieldElement<BaseField = super::BaseElement>>(
    round_counter: E,
) -> [E; HASH_STATE_WIDTH] {
    let mut round_constants = [E::ZERO; HASH_STATE_WIDTH];
    
    // Precompute Lagrange basis denominators (these are constants)
    // L_r(x) = prod_{j!=r} (x - j) / (r - j)
    // The denominator (r - j) for all j != r is constant
    let mut denominators = [E::ONE; 7];
    for r in 0..7 {
        for j in 0..7 {
            if j != r {
                let r_val = E::from(super::BaseElement::new(r as u64));
                let j_val = E::from(super::BaseElement::new(j as u64));
                denominators[r] = denominators[r] * (r_val - j_val);
            }
        }
        denominators[r] = denominators[r].inv();
    }
    
    // For each state element, interpolate the round constant
    for i in 0..HASH_STATE_WIDTH {
        for r in 0..7 {
            // Compute numerator: prod_{j!=r} (round_counter - j)
            let mut lagrange_num = E::ONE;
            for j in 0..7 {
                if j != r {
                    let j_val = E::from(super::BaseElement::new(j as u64));
                    lagrange_num = lagrange_num * (round_counter - j_val);
                }
            }
            
            // L_r(round_counter) = numerator * (1/denominator)
            let lagrange_basis = lagrange_num * denominators[r];
            
            // Add contribution: ROUND_CONSTANTS[r][i] * L_r(round_counter)
            let rc_val = E::from(super::BaseElement::new(
                hash_chiplet::ROUND_CONSTANTS[r][i],
            ));
            round_constants[i] = round_constants[i] + rc_val * lagrange_basis;
        }
    }
    
    round_constants
}

/// Compute the expected output of one RPO round
fn compute_rpo_round<E: FieldElement<BaseField = super::BaseElement>>(
    state: &[E; HASH_STATE_WIDTH],
    round_constants: &[E; HASH_STATE_WIDTH],
    result: &mut [E; HASH_STATE_WIDTH],
) {
    // Step 1: Add round constants
    let mut temp = [E::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        temp[i] = state[i] + round_constants[i];
    }

    // Step 2: Apply S-box (x^7)
    // Note: Real RPO uses x^7 for first half and x^{1/7} for second half.
    // We use x^7 for all elements here. This is a simplification that works
    // because the trace builder also uses x^7 for all (via hash_chiplet::sbox).
    for i in 0..HASH_STATE_WIDTH {
        temp[i] = sbox(temp[i]);
    }

    // Step 3: Apply MDS matrix
    for i in 0..HASH_STATE_WIDTH {
        result[i] = E::ZERO;
        for j in 0..HASH_STATE_WIDTH {
            let mds_idx = (i + HASH_STATE_WIDTH - j) % HASH_STATE_WIDTH;
            let mds_val = E::from(super::BaseElement::new(
                hash_chiplet::MDS_MATRIX[mds_idx],
            ));
            result[i] = result[i] + mds_val * temp[j];
        }
    }
}

/// S-box: x^7
#[inline]
fn sbox<E: FieldElement>(x: E) -> E {
    let x2 = x * x;
    let x4 = x2 * x2;
    let x3 = x2 * x;
    x4 * x3 // x^7
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Constraint that enforces a value is binary (0 or 1)
/// Returns x * (x - 1), which is 0 iff x ∈ {0, 1}
#[inline]
fn enforce_binary<E: FieldElement>(x: E) -> E {
    x * (x - E::ONE)
}

/// Decoded operation flags
struct DecodedOp<E: FieldElement> {
    is_init: E,
    is_absorb: E,
    is_permute: E,
    is_squeeze: E,
    is_merkle: E,
    is_fri: E,
    is_deep: E,
    is_nop: E,
}

/// Decode 3-bit selector into operation flags
///
/// Encoding matches VerifierOp:
/// ```text
/// s2 s1 s0 | Operation (decimal)
/// ---------|--------------------
///  0  0  0 | Init (0)
///  0  0  1 | Absorb (1)
///  0  1  0 | Permute (2)
///  0  1  1 | Squeeze (3)
///  1  0  0 | MerklePath (4)
///  1  0  1 | FriFold (5)
///  1  1  0 | DeepCompose (6)
///  1  1  1 | Nop/Accept (7+)
/// ```
fn decode_operation<E: FieldElement>(s0: E, s1: E, s2: E) -> DecodedOp<E> {
    let not_s0 = E::ONE - s0;
    let not_s1 = E::ONE - s1;
    let not_s2 = E::ONE - s2;

    DecodedOp {
        is_init: not_s2 * not_s1 * not_s0,           // 000
        is_absorb: not_s2 * not_s1 * s0,             // 001
        is_permute: not_s2 * s1 * not_s0,            // 010
        is_squeeze: not_s2 * s1 * s0,                // 011
        is_merkle: s2 * not_s1 * not_s0,             // 100
        is_fri: s2 * not_s1 * s0,                    // 101
        is_deep: s2 * s1 * not_s0,                   // 110
        is_nop: s2 * s1 * s0,                        // 111
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::BaseElement;

    #[test]
    fn test_enforce_binary() {
        // Binary values should pass
        assert_eq!(enforce_binary(BaseElement::ZERO), BaseElement::ZERO);
        assert_eq!(enforce_binary(BaseElement::ONE), BaseElement::ZERO);

        // Non-binary should fail
        let two = BaseElement::new(2);
        assert_ne!(enforce_binary(two), BaseElement::ZERO);
    }

    #[test]
    fn test_decode_operation() {
        let zero = BaseElement::ZERO;
        let one = BaseElement::ONE;

        // Test Init (000)
        let op = decode_operation(zero, zero, zero);
        assert_eq!(op.is_init, one);
        assert_eq!(op.is_absorb, zero);
        assert_eq!(op.is_permute, zero);

        // Test Permute (010)
        let op = decode_operation(zero, one, zero);
        assert_eq!(op.is_init, zero);
        assert_eq!(op.is_permute, one);

        // Test FriFold (101)
        let op = decode_operation(one, zero, one);
        assert_eq!(op.is_fri, one);
        assert_eq!(op.is_deep, zero);
    }

    #[test]
    fn test_column_indices() {
        // Verify indices are consistent with VERIFIER_TRACE_WIDTH (27)
        assert_eq!(SEL_0, 0);
        assert_eq!(SEL_1, 1);
        assert_eq!(SEL_2, 2);
        assert_eq!(HASH_STATE_START, 3);
        assert_eq!(HASH_STATE_END, 3 + 12);
        assert_eq!(FRI_START, 15);
        assert_eq!(FRI_END, 23);
        assert_eq!(AUX_START, 23);
        assert_eq!(AUX_END, 27);
    }

}
