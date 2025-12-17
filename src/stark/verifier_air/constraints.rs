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
//! - MerklePath/FriFold/DeepCompose: Special operations (state preserved)

use winterfell::{math::{FieldElement, StarkField}, EvaluationFrame};

use super::{
    VerifierPublicInputs, HASH_STATE_WIDTH, NUM_SELECTORS, VERIFIER_TRACE_WIDTH,
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

/// Dedicated Merkle index register column.
pub const IDX_REG: usize = FRI_END;

/// Expected-root register columns (4): the Merkle root we are currently verifying against.
pub const ROOT_REG_START: usize = IDX_REG + 1;
pub const ROOT_REG_END: usize = ROOT_REG_START + 4;

/// QueryGen step counter column: enforces qgen/export microprogram runs (prevents skipping).
pub const QGEN_CTR: usize = ROOT_REG_END;

/// Root-kind selector column: selects which public commitment root is expected (trace/comp/FRI layer).
pub const ROOT_KIND: usize = QGEN_CTR + 1;

/// Carry/register columns (8): cross-op binding (always copied unless explicitly updated).
pub const CARRY_START: usize = ROOT_KIND + 1;
pub const CARRY_END: usize = CARRY_START + 8;

/// Auxiliary column range
pub const AUX_START: usize = CARRY_END;
pub const AUX_END: usize = VERIFIER_TRACE_WIDTH;

/// Round counter index within auxiliary columns
pub const ROUND_COUNTER: usize = AUX_START; // aux[0]

// ============================================================================
// INIT KINDS (encoded via aux[0] on Init rows)
// ============================================================================
//
// NOTE: aux[0] is unconstrained on Init rows by the "round counter" constraints,
// so we re-purpose it to disambiguate Init semantics. This avoids any "allow_any"
// transitions and makes the hash transcript/Merkle computations sound.
pub const INIT_KIND_RESET_WITH_LEN: u64 = 8;
pub const INIT_KIND_LOAD_CAPACITY4: u64 = 9;
pub const INIT_KIND_COPY_DIGEST_FROM_RATE: u64 = 10;
pub const INIT_KIND_MERKLE_PREP_MERGE8: u64 = 11;
pub const INIT_KIND_LOAD_ROOT4: u64 = 12;
/// Load scratch Merkle index from persistent query index (IDX_REG → CARRY[0]).
pub const INIT_KIND_LOAD_MERKLE_IDX: u64 = 13;

// Max supported FRI layers for root-kind binding (trace=0, comp=1, fri layers at 2..=2+MAX-1).
// Must be >= the maximum FRI layers implied by protocol parameters (e.g. blowup=64, remainder=31).
// Root pool size must cover:
// - direct proofs: num_fri_layers
// - 2-child verifying aggregator: child0.fri + 2 + child1.fri (root-kind remap pool)
// Keep comfortably above any realistic configuration.
const MAX_FRI_LAYERS: usize = 32;

// ============================================================================
// CONSTRAINT EVALUATION
// ============================================================================

/// Evaluate all transition constraints
///
/// The result slice should have length equal to the number of constraint equations.
pub fn evaluate_all<E: FieldElement<BaseField = super::BaseElement>>(
    frame: &EvaluationFrame<E>,
    _periodic_values: &[E],
    result: &mut [E],
    pub_inputs: &VerifierPublicInputs,
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

    // --- 5. Compute values for RPO round verification ---
    // Winterfell round: sbox → MDS → +ARK1 → inv_sbox → MDS → +ARK2
    // 
    // To verify without computing inv_sbox:
    // 1. Compute mid = MDS(sbox(current)) + ARK1
    // 2. Compute candidate = INV_MDS(next - ARK2)
    // 3. Verify: sbox(candidate) = mid (proves candidate = inv_sbox(mid))
    
    // round_constants is ARK1 from Lagrange interpolation
    let mut mid = [E::ZERO; HASH_STATE_WIDTH];
    compute_rpo_mid(&current_hash, &round_constants, &mut mid);
    
    // Get ARK2 for this round
    let ark2 = compute_ark2_lagrange(round_counter);
    
    // Compute next - ARK2
    let mut next_minus_ark2 = [E::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        next_minus_ark2[i] = next_hash[i] - ark2[i];
    }
    
    // Apply inverse MDS to get candidate
    let mut candidate = [E::ZERO; HASH_STATE_WIDTH];
    apply_inv_mds(&next_minus_ark2, &mut candidate);

    // --- 6. Hash state constraints (12) ---
    //
    // IMPORTANT: We do NOT allow unconstrained ("allow_any") state transitions.
    // Every op must have explicit semantics enforced by constraints.
    for i in 0..HASH_STATE_WIDTH {
        // For Permute: verify sbox(candidate) = mid
        // This proves that candidate = inv_sbox(mid), validating the round
        let permute_constraint = sbox(candidate[i]) - mid[i];

        // For Nop/Squeeze: next should equal current (copy)
        let copy_constraint = next_hash[i] - current_hash[i];

        // For Absorb: capacity preserved, rate can change
        // Semantics: next_hash[0..3] == current_hash[0..3] and
        // next_hash[4+i] == current_hash[4+i] + absorbed[i] for i in 0..8.
        let absorb_constraint = if i < 4 {
            next_hash[i] - current_hash[i]
        } else {
            let j = i - 4;
            let absorbed = current[FRI_START + j];
            next_hash[i] - (current_hash[i] + absorbed)
        };

        // For Init: semantics depend on aux[0] "init kind".
        // We use 6 kinds (8,9,10,11,12,13) with degree-5 Lagrange basis polynomials.
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k11 = E::from(super::BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));
        let k13 = E::from(super::BaseElement::new(INIT_KIND_LOAD_MERKLE_IDX));

        // Ensure init kind is in {8,9,10,11,12,13} on Init rows:
        // (rc-8)(rc-9)(rc-10)(rc-11)(rc-12)(rc-13) = 0
        let init_kind_in_range =
            (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12) * (rc - k13);

        // Lagrange basis over points {8,9,10,11,12,13}:
        // denom8  = (8-9)(8-10)(8-11)(8-12)(8-13)        = -120
        // denom9  = (9-8)(9-10)(9-11)(9-12)(9-13)        = 24
        // denom10 = (10-8)(10-9)(10-11)(10-12)(10-13)    = -12
        // denom11 = (11-8)(11-9)(11-10)(11-12)(11-13)    = 12
        // denom12 = (12-8)(12-9)(12-10)(12-11)(12-13)    = -24
        // denom13 = (13-8)(13-9)(13-10)(13-11)(13-12)    = 120
        let inv24 = E::from(super::BaseElement::new(17678129733188976641u64)); // 24^{-1}
        let inv_neg24 = E::ZERO - inv24;
        let inv_neg120 = E::from(super::BaseElement::new(153722867245121536u64)); // (-120)^{-1}
        let inv120 = E::ZERO - inv_neg120;
        let inv12 = E::from(super::BaseElement::new(12)).inv();
        let inv_neg12 = E::ZERO - inv12;

        let l8 = (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12) * (rc - k13) * inv_neg120;
        let l9 = (rc - k8) * (rc - k10) * (rc - k11) * (rc - k12) * (rc - k13) * inv24;
        let l10 = (rc - k8) * (rc - k9) * (rc - k11) * (rc - k12) * (rc - k13) * inv_neg12;
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * (rc - k13) * inv12;
        let l12 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * (rc - k13) * inv_neg24;
        let l13 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12) * inv120;

        // Kind 8: reset to all-zeros with state[0] = fri[0] (length/domain-sep).
        let expected_reset = if i == 0 { current[FRI_START] } else { E::ZERO };
        let init_reset_constraint = next_hash[i] - expected_reset;

        // Kind 9: load capacity[0..3] from fri[0..3], zero out the rest.
        let expected_load = if i < 4 { current[FRI_START + i] } else { E::ZERO };
        let init_load_constraint = next_hash[i] - expected_load;

        // Kind 10: copy digest from rate[0..3] (hash_state[4..7]) into capacity[0..3], zero out rest.
        let expected_copy = if i < 4 { current_hash[4 + i] } else { E::ZERO };
        let init_copy_constraint = next_hash[i] - expected_copy;

        // Kind 11: prepare a Merkle merge hash_elements([left||right]) with len=8.
        // Inputs live in the CURRENT row:
        // - digest in current_hash[0..3]
        // - sibling in fri[0..3]
        // - direction bit in fri[5] (0 => current is left child; 1 => current is right child)
        //
        // Output (NEXT row hash state):
        // - next_hash[0] = 8
        // - next_hash[1..3] = 0
        // - next_hash[4..7] = left
        // - next_hash[8..11] = right
        let dir = current[FRI_START + 5];
        let one_minus_dir = E::ONE - dir;
        let expected_merkle = if i == 0 {
            // len = 8
            E::from(super::BaseElement::new(8))
        } else if i < 4 {
            // capacity cleared
            E::ZERO
        } else if i < 8 {
            // left[j] where j = i-4
            let j = i - 4;
            let digest_j = current_hash[j];
            let sibling_j = current[FRI_START + j];
            one_minus_dir * digest_j + dir * sibling_j
        } else {
            // right[j] where j = i-8
            let j = i - 8;
            let digest_j = current_hash[j];
            let sibling_j = current[FRI_START + j];
            one_minus_dir * sibling_j + dir * digest_j
        };
        let init_merkle_constraint = next_hash[i] - expected_merkle;

        // Kind 12: load expected-root register (root_reg) from fri[0..3], while copying hash_state.
        let init_rootload_constraint = next_hash[i] - current_hash[i];

        // Kind 13: load scratch Merkle index into carry column(s); hash_state is copied.
        let init_load_merkle_idx_constraint = next_hash[i] - current_hash[i];

        // Combine init constraints by kind selector.
        // Also enforce init kind range on ALL init rows by adding the cubic constraint once (i==0).
        let init_constraint =
            l8 * init_reset_constraint
                + l9 * init_load_constraint
                + l10 * init_copy_constraint
                + l11 * init_merkle_constraint
                + l12 * init_rootload_constraint
                + l13 * init_load_merkle_idx_constraint
                + if i == 0 { init_kind_in_range } else { E::ZERO };

        // Combine constraints based on operation.
        //
        // - Init: explicit semantics (no unconstrained jumps)
        // - MerklePath/FriFold/DeepCompose/Nop: state preserved (copy)
        let constraint = op.is_permute * permute_constraint
            + op.is_squeeze * copy_constraint
            + op.is_absorb * absorb_constraint
            + op.is_init * init_constraint
            + (op.is_merkle + op.is_fri + op.is_deep + op.is_nop) * copy_constraint;

        result[idx] = constraint;
        idx += 1;
    }

    // --- 7. FRI/DEEP working constraints (8) ---
    // Decode NEXT row operation to allow changes going INTO special ops
    let next_op = decode_operation(next[SEL_0], next[SEL_1], next[SEL_2]);
    
    // Compute "is special" flags (each is 0 or 1 due to mutually exclusive flags)
    let op_special = op.is_merkle + op.is_fri + op.is_deep + op.is_init + op.is_absorb;
    // IMPORTANT: include Absorb in "next special" as Absorb rows legitimately mutate fri columns.
    let next_special = next_op.is_merkle + next_op.is_fri + next_op.is_deep + next_op.is_init + next_op.is_absorb;
    
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
    
    // Opened pair (as committed in the FRI layer Merkle leaf).
    let fx_open = current[FRI_START];
    let fnegx_open = current[FRI_START + 1];
    // x is taken from carry[1] (computed once per query, then squared across layers).
    let x = current[CARRY_START + 1];
    let beta = current[FRI_START + 3];
    let g = current[FRI_START + 4];
    
    // SECURITY: bind swap ordering via carry[5] (upper-half bit derived in-trace).
    // b=0 => (f(x), f(-x)) = (fx_open, fnegx_open)
    // b=1 => (f(x), f(-x)) = (fnegx_open, fx_open)
    let b = current[CARRY_START + 5];
    let one_minus_b = E::ONE - b;
    let f_x = one_minus_b * fx_open + b * fnegx_open;
    let f_neg_x = b * fx_open + one_minus_b * fnegx_open;
    
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
    // ========================================================================
    
    let ood_lhs = current[FRI_START + 6]; // Pre-computed LHS
    let ood_rhs = current[FRI_START + 7]; // Pre-computed RHS
    
    // OOD constraint: LHS must equal RHS
    // MUST match R1CS implementation in ood_eval_r1cs.rs exactly!
    let _ood_constraint = ood_lhs - ood_rhs;
    
    // ========================================================================
    // DEEP COMPOSE VERIFICATION MODES (aux[2] determines mode)
    // 
    // aux[2] = 0: ROOT mode - verify hash_state[0..3] == fri[0..3] (Merkle root)
    // aux[2] = 1: OOD mode - verify fri[6] == fri[7] (OOD LHS == RHS)
    // aux[2] = 2: TERMINAL mode - verify fri[6] == fri[7] (FRI final == expected)
    // aux[2] = 3: DEEP mode - verify fri[6] == fri[7] (DEEP computed == expected)
    // aux[2] = 4: STATEMENT mode - verify hash_state[0..3] == pub_inputs.statement_hash
    // aux[2] = 5: PARAMS mode - verify hash_state[0..3] matches expected params digest
    // aux[2] = 6: (unused)
    // ========================================================================
    let aux_mode = current[AUX_START + 2];
    let one = E::ONE;
    let two = E::from(super::BaseElement::new(2));
    let three = E::from(super::BaseElement::new(3));
    let four = E::from(super::BaseElement::new(4));
    let five = E::from(super::BaseElement::new(5));
    let six = E::from(super::BaseElement::new(6));
    
    // Statement hash binding constraints (mode 4)
    // When aux[2] = 4, verify hash_state matches public input statement_hash
    // This ensures the prover verified the ACTUAL commitments, not fake ones
    let statement_constraint_0 = current_hash[0] - E::from(pub_inputs.statement_hash[0]);
    let statement_constraint_1 = current_hash[1] - E::from(pub_inputs.statement_hash[1]);
    let statement_constraint_2 = current_hash[2] - E::from(pub_inputs.statement_hash[2]);
    let statement_constraint_3 = current_hash[3] - E::from(pub_inputs.statement_hash[3]);
    
    // Params digest binding constraints (mode 5)
    // When aux[2] = 5, verify hash_state matches public input params_digest.
    let params_constraint_0 = current_hash[0] - E::from(pub_inputs.params_digest[0]);
    let params_constraint_1 = current_hash[1] - E::from(pub_inputs.params_digest[1]);
    let params_constraint_2 = current_hash[2] - E::from(pub_inputs.params_digest[2]);
    let params_constraint_3 = current_hash[3] - E::from(pub_inputs.params_digest[3]);
    
    // Root verification: hash_state[i] == root_reg[i] for i in 0..4.
    //
    // SECURITY: `root_reg` is updated only via Init(kind=LOAD_CAPACITY4) and then reused
    // for Merkle root checks, preventing the prover from choosing an unconstrained expected root.
    let root_constraint_0 = current_hash[0] - current[ROOT_REG_START + 0];
    let root_constraint_1 = current_hash[1] - current[ROOT_REG_START + 1];
    let root_constraint_2 = current_hash[2] - current[ROOT_REG_START + 2];
    let root_constraint_3 = current_hash[3] - current[ROOT_REG_START + 3];
    
    // Equality constraint: fri[6] == fri[7] (for OOD, TERMINAL, DEEP modes)
    let equality_constraint = current[FRI_START + 6] - current[FRI_START + 7];

    // Additional binding constraints for DEEP verification (DeepCompose mode 3):
    // fri[6] must be selected_f * (x - z) * (x - z*g)
    // fri[7] must be carry[3]*(x - z*g) + carry[4]*(x - z)
    //
    // Row layout for mode 3:
    // - fri[0] = z
    // - fri[1] = f_x
    // - fri[2] = f_neg_x
    let z_val = current[FRI_START + 0];
    let fx0 = current[FRI_START + 1];
    let fneg0 = current[FRI_START + 2];
    let x0 = current[CARRY_START + 1];
    let g_trace = E::from(pub_inputs.g_trace);
    let zg = z_val * g_trace;
    let den_z = x0 - z_val;
    let den_zg = x0 - zg;
    let denom = den_z * den_zg;
    let b0 = current[CARRY_START + 5];
    let one_minus_b0 = E::ONE - b0;
    let selected_f = one_minus_b0 * fx0 + b0 * fneg0;
    let deep_lhs = selected_f * denom;
    let deep_rhs = current[CARRY_START + 3] * den_zg + current[CARRY_START + 4] * den_z;

    let bind_deep_lhs = current[FRI_START + 6] - deep_lhs;
    let bind_deep_rhs = current[FRI_START + 7] - deep_rhs;

    // DeepCompose mode selector for DEEP check (aux[2]=3) over {0..=6}.
    // Non-zero only when aux_mode == 3.
    let is_deep_check = aux_mode
        * (aux_mode - one)
        * (aux_mode - two)
        * (aux_mode - four)
        * (aux_mode - five)
        * (aux_mode - six);

    // DeepCompose mode selector for generic linkage checks (aux[2]=6) over {0..=6}.
    // Non-zero only when aux_mode == 6.
    let is_link_check = aux_mode
        * (aux_mode - one)
        * (aux_mode - two)
        * (aux_mode - three)
        * (aux_mode - four)
        * (aux_mode - five);

    // Link-check row layout (aux[2]=6):
    // - fri[0] = next_f_x
    // - fri[1] = next_f_neg_x
    // - fri[6] = prev_fold (carry[7])
    // - fri[7] = selected(next_f_x,next_f_neg_x) based on carry[5]
    let next_fx = current[FRI_START + 0];
    let next_fneg = current[FRI_START + 1];
    let b_link = current[CARRY_START + 5];
    let one_minus_b_link = E::ONE - b_link;
    let selected_next = one_minus_b_link * next_fx + b_link * next_fneg;
    let bind_link_lhs = current[FRI_START + 6] - current[CARRY_START + 7];
    let bind_link_rhs = current[FRI_START + 7] - selected_next;

    // Terminal-check selector (aux[2]=2) over {0..=6}: non-zero only at 2.
    let is_terminal_check = aux_mode
        * (aux_mode - one)
        * (aux_mode - three)
        * (aux_mode - four)
        * (aux_mode - five)
        * (aux_mode - six);

    // Terminal-check row layout (aux[2]=2):
    // - carry[7] = final folded value (from the last FRI fold)
    // - carry[3] = Horner accumulator over remainder coeffs (fixed 32 steps, Nop(mode=18))
    // - carry[4] = Horner step counter (must be 32 at terminal check)
    // - fri[6] = final folded value (lhs), must bind to carry[7]
    // - fri[7] = expected value (rhs), must bind to carry[3]
    let bind_term_lhs = current[FRI_START + 6] - current[CARRY_START + 7];
    let bind_term_rhs = current[FRI_START + 7] - current[CARRY_START + 3];
    let thirty_two = E::from(super::BaseElement::new(32));
    let bind_term_ctr = current[CARRY_START + 4] - thirty_two;

    // Nop sub-mode selectors.
    //
    // SECURITY: On Nop rows we restrict aux[2] to a small set of mode tags, and then use
    // Lagrange basis polynomials to activate different constraint sub-systems.
    //
    // Allowed Nop sub-modes: {0,6,7,8,9,10,11,12,13,14,15,16,17,18}
    // - 6  : QueryGen (bit/shift + accumulator)
    // - 8  : ZeroCheck (fri[4] == 0), used to bind terminal quotient = 0
    // - 9  : Canonicality check for Goldilocks u64 extraction (see below)
    // - 10 : PoWShift (QueryGen shift with bit forced to 0)
    // - 11 : Capture binding (fri[4] == hash_state[0]) to bind derived integers to transcript
    // - 14 : CaptureIdx binding (fri[4] == IDX_REG) to derive masked indices / bits from Q_IDX
    // - 15 : StoreAccToMerkleIdx (carry[0] := fri[6]) to seed Merkle microprogram with masked idx
    let seven = E::from(super::BaseElement::new(7));
    let eight = E::from(super::BaseElement::new(8));
    let nine = E::from(super::BaseElement::new(9));
    let ten = E::from(super::BaseElement::new(10));
    let eleven = E::from(super::BaseElement::new(11));

    let twelve = E::from(super::BaseElement::new(12));
    let thirteen = E::from(super::BaseElement::new(13));
    let fourteen = E::from(super::BaseElement::new(14));
    let fifteen = E::from(super::BaseElement::new(15));
    let sixteen = E::from(super::BaseElement::new(16));
    let seventeen = E::from(super::BaseElement::new(17));
    let eighteen = E::from(super::BaseElement::new(18));

    // Denominator inverses for Lagrange basis over points {0,6,7,8,9,10,11,12,13,14,15,16,17,18}.
    //
    // NOTE: we keep the interpolation set (including 7) even though 7 is disallowed by the
    // "allowed Nop sub-modes" constraint below; the basis polynomials still evaluate to the
    // correct 0/1 indicators on the remaining allowed points, and this avoids re-deriving
    // constants.
    //
    // Precomputed in Goldilocks:
    // denom6  = -239500800
    // denom8  = -5806080
    // denom9  = 2177280
    // denom10 = -1209600
    // denom11 = 950400
    // denom12 = -1036800
    // denom13 = 1572480
    // denom14 = -3386880
    // denom15 = 10886400
    // denom16 = -58060800
    // denom17 = 678585600
    let inv_neg_239500800 = E::from(super::BaseElement::new(13493303875880579883u64));
    let inv_neg_5806080 = E::from(super::BaseElement::new(7808148814990036624u64));
    let inv_2177280 = E::from(super::BaseElement::new(9922843275717542871u64));
    let inv_neg_1209600 = E::from(super::BaseElement::new(15343021428654674610u64));
    let inv_950400 = E::from(super::BaseElement::new(12335076119791968869u64));
    let inv_neg_1036800 = E::from(super::BaseElement::new(17900191666763787045u64));
    let inv_1572480 = E::from(super::BaseElement::new(12320341145653937489u64));
    let inv_neg_3386880 = E::from(super::BaseElement::new(209152204686788269u64));
    let inv_10886400 = E::from(super::BaseElement::new(16741963910675176031u64));
    let inv_neg_58060800 = E::from(super::BaseElement::new(11848861323147754255u64));
    let inv_678585600 = E::from(super::BaseElement::new(8258888563393619562u64));

    // Enforce Nop sub-mode is in {0,6,7,8,9,10,11,12,13,14,15,16,17} on Nop rows:
    // aux*(aux-6)(aux-7)(aux-8)(aux-9)(aux-10)(aux-11)(aux-12)(aux-13)(aux-14)(aux-15)(aux-16)(aux-17)(aux-18) = 0
    let nop_mode_in_range = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * (aux_mode - eighteen);

    // Horner-step selector for terminal remainder evaluation (Nop(mode=18)).
    // Lagrange basis over points {0,6..=18}.
    let inv_denom_18 = (eighteen
        * (eighteen - six)
        * (eighteen - seven)
        * (eighteen - eight)
        * (eighteen - nine)
        * (eighteen - ten)
        * (eighteen - eleven)
        * (eighteen - twelve)
        * (eighteen - thirteen)
        * (eighteen - fourteen)
        * (eighteen - fifteen)
        * (eighteen - sixteen)
        * (eighteen - seventeen))
        .inv();
    let is_horner = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_denom_18;
    let is_horner_nop = op.is_nop * is_horner;

    // L_7(x) over {0,6,7,8,9,10,11,12,13,14,15,16,17} has denom = 25401600.
    let inv_25401600 = E::from(super::BaseElement::new(9810376543062873202u64));
    let is_deepacc = aux_mode
        * (aux_mode - six)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_25401600
        * (aux_mode - eighteen)
        * (seven - eighteen).inv();

    // L_6(x) over {0,6,7,8,9,10,11,12,13,14,15,16,17} has denom = -239500800.
    let is_qgen = aux_mode
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_neg_239500800
        * (aux_mode - eighteen)
        * (six - eighteen).inv();
    // L_8(x) denom = -5806080
    let is_zerocheck = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_neg_5806080
        * (aux_mode - eighteen)
        * (eight - eighteen).inv();
    // L_9(x) denom = 2177280
    let is_canon = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_2177280
        * (aux_mode - eighteen)
        * (nine - eighteen).inv();
    // L_10(x) denom = -1209600
    let is_powshift = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_neg_1209600
        * (aux_mode - eighteen)
        * (ten - eighteen).inv();
    // L_11(x) denom = 950400
    let is_capture = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_950400
        * (aux_mode - eighteen)
        * (eleven - eighteen).inv();
    // L_12(x) denom = -1036800
    let is_export = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_neg_1036800
        * (aux_mode - eighteen)
        * (twelve - eighteen).inv();
    // L_13(x) denom = 1572480
    let is_freeze = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_1572480
        * (aux_mode - eighteen)
        * (thirteen - eighteen).inv();

    // L_14(x) denom = -3386880
    let is_capture_idx = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_neg_3386880
        * (aux_mode - eighteen)
        * (fourteen - eighteen).inv();

    // L_15(x) denom = 10886400
    let is_store_acc = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - sixteen)
        * (aux_mode - seventeen)
        * inv_10886400
        * (aux_mode - eighteen)
        * (fifteen - eighteen).inv();

    // L_16(x) denom = -58060800
    let is_xexp_step = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - seventeen)
        * inv_neg_58060800
        * (aux_mode - eighteen)
        * (sixteen - eighteen).inv();

    // L_17(x) denom = 678585600
    let is_xexp_init = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * (aux_mode - fourteen)
        * (aux_mode - fifteen)
        * (aux_mode - sixteen)
        * inv_678585600
        * (aux_mode - eighteen)
        * (seventeen - eighteen).inv();

    let is_qgen_nop = op.is_nop * is_qgen;
    let is_zerocheck_nop = op.is_nop * is_zerocheck;
    let is_canon_nop = op.is_nop * is_canon;
    let is_powshift_nop = op.is_nop * is_powshift;
    let is_capture_nop = op.is_nop * is_capture;
    let is_export_nop = op.is_nop * is_export;
    let is_freeze_nop = op.is_nop * is_freeze;
    let is_capture_idx_nop = op.is_nop * is_capture_idx;
    let is_store_acc_nop = op.is_nop * is_store_acc;
    let is_xexp_step_nop = op.is_nop * is_xexp_step;
    let is_xexp_init_nop = op.is_nop * is_xexp_init;
    let is_deepacc_nop = op.is_nop * is_deepacc;
    
    for i in 0..8 {
        let fri_curr = current[FRI_START + i];
        let fri_next = next[FRI_START + i];
        let copy_constraint = fri_next - fri_curr;

        // Selector for Init-kind 11 (Merkle merge prep): l11 over {8,9,10,11,12,13}.
        // We recompute it here because we need it for fri-column semantics.
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));
        let k13 = E::from(super::BaseElement::new(INIT_KIND_LOAD_MERKLE_IDX));
        // denom11 = 12 over {8..=13}
        let inv12 = E::from(super::BaseElement::new(12)).inv();
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * (rc - k13) * inv12;

        if i == 4 {
            // FRI folding result verification
            // Column 4 is used as scratch across phases, so we MUST enforce copy on non-special transitions.
            //
            // NOTE: the Merkle index register is now a dedicated column (`IDX_REG`), so this column no longer
            // carries Merkle idx semantics.
            // On QueryGen Nop rows, we repurpose fri[4] as an integer shift register:
            //   fri4_cur = 2*fri4_next + fri5_cur
            // (with fri5 constrained binary).
            //
            // IMPORTANT (soundness): for column 4, we MUST chain capture/canonicality rows into
            // the subsequent decomposition rows. Otherwise the prover can "capture then swap"
            // or "canon then swap" and decompose a different limb.
            //
            // So we do NOT disable copy on capture/canon rows for this column.
            let copy_ok = both_not_special
                * (one
                    - is_qgen_nop
                    - is_deepacc_nop
                    - is_zerocheck_nop
                    - is_powshift_nop
                    - is_export_nop
                    - is_freeze_nop
                    - is_capture_idx_nop
                    - is_xexp_step_nop
                    - is_xexp_init_nop);
            let qgen_shift = fri_curr - (two * fri_next + current[FRI_START + 5]);
            let zerocheck_constraint = fri_curr; // enforce fri[4] == 0
            // Capture binding: fri[4] == hash_state[0]
            let capture_constraint = fri_curr - current_hash[0];
            // CaptureIdx binding: fri[4] == IDX_REG (persistent query index).
            let capture_idx_constraint = fri_curr - current[IDX_REG];
            // XExp init binding: fri[4] == IDX_REG (persistent query index).
            let xexp_init_constraint = fri_curr - current[IDX_REG];
            // Export binding targets IDX_REG; fri[4] is left as scratch.
            // Canonicality check (Goldilocks u64 extraction):
            //
            // Goldilocks has a rare 64-bit ambiguity for very small values: x and x+p can both fit in u64.
            // To prevent the prover from choosing the "x+p" decomposition (which can alter low bits),
            // we enforce the stronger condition: hi32 != (2^32-1).
            //
            // This rejects a 2^-32 fraction of values (including x = p-1), but removes the FS knob cleanly.
            //
            // Store:
            //   fri[4] = hi32
            //   fri[5] = w (inverse witness for hi32 - (2^32-1))
            // Enforce:
            //   (hi32 - (2^32-1)) * w = 1
            let all_ones_32 = E::from(super::BaseElement::new(0xFFFF_FFFFu64));
            let hi32 = fri_curr;
            let w = current[FRI_START + 5];
            let canon_eq = (hi32 - all_ones_32) * w - E::ONE;

            result[idx] = op.is_fri * fri_fold_constraint
                + copy_ok * copy_constraint
                + (is_qgen_nop + is_powshift_nop + is_freeze_nop + is_xexp_step_nop) * qgen_shift
                + is_zerocheck_nop * zerocheck_constraint
                + is_capture_nop * capture_constraint
                + is_capture_idx_nop * capture_idx_constraint
                + is_xexp_init_nop * xexp_init_constraint
                + is_canon_nop * canon_eq;
        } else if i == 6 {
            // Equality verification on ALL DeepCompose rows.
            // Trace builder must ensure fri[6]==fri[7] also in modes 0/4/5 (set both to 0).
            // On QueryGen Nop rows, fri[6] is an accumulator updated as:
            //   acc_next = acc_cur + bit * pow2
            // with bit = fri5_cur, pow2 = fri7_cur.
            let copy_ok = both_not_special
                * (one
                    - is_qgen_nop
                    - is_powshift_nop
                    - is_capture_idx_nop
                    - is_export_nop
                    );
            let acc_update = fri_next - (fri_curr + current[FRI_START + 5] * current[FRI_START + 7]);
            let acc_copy = fri_next - fri_curr;
            // Capture mode anchors accumulator at 0.
            let capture_acc_zero = is_capture_nop * fri_curr;
            // CaptureIdx anchors accumulator at 0.
            let capture_idx_acc_zero = is_capture_idx_nop * fri_curr;
            // XExp init anchors accumulator at 0.
            let xexp_init_acc_zero = is_xexp_init_nop * fri_curr;
            // Equality verification on ALL DeepCompose rows.
            // Trace builder must ensure fri[6]==fri[7] also in modes 0/4/5 (set both to 0).
            result[idx] = op.is_deep * equality_constraint
                + op.is_deep * is_deep_check * bind_deep_lhs
                + op.is_deep * is_deep_check * bind_deep_rhs
                + op.is_deep * is_link_check * bind_link_lhs
                + op.is_deep * is_link_check * bind_link_rhs
                + op.is_deep * is_terminal_check * bind_term_lhs
                + op.is_deep * is_terminal_check * bind_term_rhs
                + op.is_deep * is_terminal_check * bind_term_ctr
                + copy_ok * copy_constraint
                + (is_qgen_nop + is_powshift_nop) * acc_update
                + is_freeze_nop * acc_copy
                + capture_acc_zero
                + capture_idx_acc_zero
                + xexp_init_acc_zero
                ;
        } else if i < 4 {
            // Root verification for mode 0: hash_state == fri[0..3]
            // Use factors to exclude modes 4,5,6 from root check.
            // is_root_check = Π_{k=1..6}(aux[2]-k) = non-zero only when aux[2]=0
            let is_root_check = (aux_mode - one)
                * (aux_mode - two)
                * (aux_mode - three)
                * (aux_mode - four)
                * (aux_mode - five)
                * (aux_mode - six);
            let root_constraint = match i {
                0 => root_constraint_0,
                1 => root_constraint_1,
                2 => root_constraint_2,
                _ => root_constraint_3,
            };
            
            // Statement hash verification for mode 4
            // is_statement_check = aux[2]*(aux[2]-1)*(aux[2]-2)*(aux[2]-3)*(aux[2]-5)*(aux[2]-6)
            // = non-zero only when aux[2]=4
            let is_statement_check = aux_mode
                * (aux_mode - one)
                * (aux_mode - two)
                * (aux_mode - three)
                * (aux_mode - five)
                * (aux_mode - six);
            let statement_constraint = match i {
                0 => statement_constraint_0,
                1 => statement_constraint_1,
                2 => statement_constraint_2,
                _ => statement_constraint_3,
            };
            
            // Params digest verification for mode 5
            // is_params_check = aux[2]*(aux[2]-1)*(aux[2]-2)*(aux[2]-3)*(aux[2]-4)*(aux[2]-6)
            // = non-zero only when aux[2]=5
            let is_params_check = aux_mode
                * (aux_mode - one)
                * (aux_mode - two)
                * (aux_mode - three)
                * (aux_mode - four)
                * (aux_mode - six);
            let params_constraint = match i {
                0 => params_constraint_0,
                1 => params_constraint_1,
                2 => params_constraint_2,
                _ => params_constraint_3,
            };
            
            // Allow DeepAcc Nop rows (aux[2]=7) to overwrite fri[0..3] with DEEP accumulator inputs.
            let copy_ok = both_not_special * (E::ONE - is_deepacc_nop);
            result[idx] = op.is_deep * is_root_check * root_constraint
                + op.is_deep * is_statement_check * statement_constraint
                + op.is_deep * is_params_check * params_constraint
                + copy_ok * copy_constraint
                + if i == 0 { op.is_nop * nop_mode_in_range } else { E::ZERO };
        } else {
            // Columns 5, 7: copy constraint only
            if i == 5 {
                // For Init kind 11, enforce dir bit in fri[5] is binary.
                let dir = fri_curr;
                // On QueryGen Nop rows, fri[5] is the extracted bit and must be binary,
                // and it is allowed to change (disable copy).
                let copy_ok = both_not_special
                    * (one
                        - is_qgen_nop
                        - is_deepacc_nop
                        - is_zerocheck_nop
                        - is_canon_nop
                        - is_powshift_nop
                        - is_capture_nop
                        - is_capture_idx_nop
                        - is_export_nop
                        - is_freeze_nop
                        - is_store_acc_nop
                        - is_xexp_step_nop
                        - is_xexp_init_nop);
                let qgen_bit = fri_curr * (fri_curr - one);

                result[idx] = copy_ok * copy_constraint
                    + op.is_init * l11 * enforce_binary(dir)
                    + is_qgen_nop * qgen_bit;
                // PoWShift: enforce bit==0
                result[idx] = result[idx] + is_powshift_nop * fri_curr;
                // CaptureIdx: anchor bit==0 (shift seed).
                result[idx] = result[idx] + is_capture_idx_nop * fri_curr;
                // XExp init/step: anchor bit==0 on init, binary on steps.
                result[idx] = result[idx] + is_xexp_init_nop * fri_curr;
                result[idx] = result[idx] + is_xexp_step_nop * qgen_bit;
                // Freeze mode uses fri[5] as the bit; enforce bit binary.
                result[idx] = result[idx] + is_freeze_nop * qgen_bit;
                // Canonicality mode does not impose any constraints on fri[5] here (fri[5] is used as inverse witness).
            } else {
                // i == 7: on QueryGen Nop rows, fri[7] is pow2 and doubles each step:
                //   pow2_next = 2 * pow2_cur.
                let copy_ok = both_not_special
                    * (one
                        - is_qgen_nop
                        - is_deepacc_nop
                        - is_zerocheck_nop
                        - is_canon_nop
                        - is_powshift_nop
                        - is_capture_idx_nop
                        - is_export_nop
                        - is_xexp_step_nop
                        - is_xexp_init_nop
                        - is_horner_nop
                        );
                let pow2_update = fri_next - (two * fri_curr);
                // Capture mode anchors pow2 at 1.
                let capture_pow2_one = is_capture_nop * (fri_curr - one);
                // CaptureIdx anchors pow2 at 1.
                let capture_idx_pow2_one = is_capture_idx_nop * (fri_curr - one);
                result[idx] = copy_ok * copy_constraint
                    + (is_qgen_nop + is_powshift_nop) * pow2_update
                    + capture_pow2_one
                    + capture_idx_pow2_one
                    // XExp init/step: anchor pow2==1 and keep it constant.
                    + is_xexp_init_nop * (fri_curr - one)
                    // Allow transition out of XExp into a special op to overwrite fri[7].
                    + is_xexp_step_nop * (E::ONE - next_special) * (fri_next - fri_curr);
            }
        }
        idx += 1;
    }

    // --- 8. Index register constraints (1) ---
    //
    // Persistent query index register (Q_IDX):
    // - Default: copy
    // - On Export Nop rows (aux[2]=12): idx_next = fri[6] (accumulator)
    {
        let idx_curr = current[IDX_REG];
        let idx_next = next[IDX_REG];
        let copy_constraint = idx_next - idx_curr;

        // Export: idx_next = acc (fri[6]) on aux[2]=12 Nop rows.
        let export_constraint = idx_next - current[FRI_START + 6];
        let export_term = is_export_nop * export_constraint;

        // CONTROL-FLOW HARDENING (export): require export rows are preceded by the terminal
        // ZeroCheck row (aux[2]=8), which ensures the decompose gadget ran to completion.
        // We enforce this by looking at the *next* row:
        //   if next row is export_nop, current row must be zerocheck_nop.
        let next_mode = next[AUX_START + 2];
        // Selector for export (aux[2]=12) over {0,6,7,8,9,10,11,12,13,14,15,16,17}:
        // denom12 = -1036800.
        let inv_neg_1036800 = E::from(super::BaseElement::new(17900191666763787045u64));
        let fourteen = E::from(super::BaseElement::new(14));
        let fifteen = E::from(super::BaseElement::new(15));
        let sixteen = E::from(super::BaseElement::new(16));
        let seventeen = E::from(super::BaseElement::new(17));
        let next_is_export = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - eleven)
            * (next_mode - thirteen)
            * (next_mode - fourteen)
            * (next_mode - fifteen)
            * (next_mode - sixteen)
            * (next_mode - seventeen)
            * inv_neg_1036800
            * (next_mode - E::from(super::BaseElement::new(18)))
            * (twelve - E::from(super::BaseElement::new(18))).inv();
        let next_is_export_nop = next_op.is_nop * next_is_export;
        let export_requires_prev_zerocheck = next_is_export_nop * (E::ONE - is_zerocheck_nop);

        // Copy by default, except on export rows.
        let copy_ok = E::ONE - is_export_nop;
        result[idx] = copy_ok * copy_constraint
            + export_term
            + export_requires_prev_zerocheck;
        idx += 1;
    }

    // --- 9. QueryGen step counter constraints (1) ---
    //
    // SECURITY: force the capture→64-step qgen→zerocheck→export microprogram to actually run.
    // qgen_ctr semantics:
    // - On capture rows (aux[2]=11): next qgen_ctr = 0
    // - On qgen/powshift/freeze rows (aux[2] in {6,10,13}): next = cur + 1
    // - Otherwise: copy
    // Additionally, on export rows we require qgen_ctr == 64, and also on the immediately preceding
    // zerocheck row (because export_requires_prev_zerocheck enforces the predecessor exists).
    {
        let ctr_cur = current[QGEN_CTR];
        let ctr_next = next[QGEN_CTR];
        let copy = ctr_next - ctr_cur;
        let inc = ctr_next - (ctr_cur + E::ONE);
        let reset = ctr_next; // == 0

        let inc_mode = is_qgen_nop + is_powshift_nop + is_freeze_nop;
        let capture_begin = is_capture_nop + is_capture_idx_nop;
        let other_mode = E::ONE - capture_begin - inc_mode;

        // Force export rows to have ctr==64.
        let sixty_four = E::from(super::BaseElement::new(64));
        let export_requires_ctr = is_export_nop * (ctr_cur - sixty_four);

        // Force the row before an export to also have ctr==64 (prevents fake zerocheck→export).
        let next_mode = next[AUX_START + 2];
        let six = E::from(super::BaseElement::new(6));
        let seven = E::from(super::BaseElement::new(7));
        let eight = E::from(super::BaseElement::new(8));
        let nine = E::from(super::BaseElement::new(9));
        let ten = E::from(super::BaseElement::new(10));
        let eleven = E::from(super::BaseElement::new(11));
        let twelve = E::from(super::BaseElement::new(12));
        let thirteen = E::from(super::BaseElement::new(13));

        let next_is_export = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - eleven)
            * (next_mode - thirteen)
            * (next_mode - fourteen)
            * (next_mode - fifteen)
            * (next_mode - sixteen)
            * (next_mode - seventeen)
            * inv_neg_1036800
            * (next_mode - E::from(super::BaseElement::new(18)))
            * (twelve - E::from(super::BaseElement::new(18))).inv();
        let next_is_export_nop = next_op.is_nop * next_is_export;
        let prev_export_requires_ctr = next_is_export_nop * (ctr_cur - sixty_four);

        // Allow the counter to reset at the start of a new microprogram: disable the "copy" constraint
        // on transitions INTO a capture-begin row (aux[2]=11 or 14 on NEXT row).
        // Selector for capture (aux[2]=11) over {0,6,7,8,9,10,11,12,13,14,15,16,17}:
        // denom11 = 950400.
        let inv_950400 = E::from(super::BaseElement::new(12335076119791968869u64));
        let next_is_capture = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - twelve)
            * (next_mode - thirteen)
            * (next_mode - fourteen)
            * (next_mode - fifteen)
            * (next_mode - sixteen)
            * (next_mode - seventeen)
            * inv_950400
            * (next_mode - E::from(super::BaseElement::new(18)))
            * (eleven - E::from(super::BaseElement::new(18))).inv();
        // Selector for capture-idx (aux[2]=14) over {0,6,7,8,9,10,11,12,13,14,15,16,17}:
        // denom14 = -3386880.
        let inv_neg_3386880 = E::from(super::BaseElement::new(209152204686788269u64));
        let next_is_capture_idx = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - eleven)
            * (next_mode - twelve)
            * (next_mode - thirteen)
            * (next_mode - fifteen)
            * (next_mode - sixteen)
            * (next_mode - seventeen)
            * inv_neg_3386880
            * (next_mode - E::from(super::BaseElement::new(18)))
            * (fourteen - E::from(super::BaseElement::new(18))).inv();

        let next_is_capture_begin_nop = next_op.is_nop * (next_is_capture + next_is_capture_idx);

        result[idx] = capture_begin * reset
            + inc_mode * inc
            + other_mode * (E::ONE - next_is_capture_begin_nop) * copy
            + export_requires_ctr
            + prev_export_requires_ctr;
        idx += 1;
    }

    // --- 10. Expected-root register constraints (4) ---
    //
    // These 4 columns store the expected Merkle root digest for the *current* commitment tree.
    // They are updated only on Init(kind=LOAD_ROOT4) rows:
    //   root_next[i] = fri_curr[i]
    // and copied otherwise.
    //
    // This lets the prover "load" the expected root (from parsed proof commitments) in a constrained
    // way before verifying Merkle paths, and then root-check rows (DeepCompose mode 0) compare
    // hash_state[0..3] against root_reg[0..3].
    {
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k11 = E::from(super::BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8));
        let inv24 = E::from(super::BaseElement::new(17678129733188976641u64)); // 24^{-1}
        // Lagrange selector for kind=12 over points {8,9,10,11,12}.
        // l12 = (rc-8)(rc-9)(rc-10)(rc-11) / 24
        let l12 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * inv24;
        let is_load_root = op.is_init * l12;

        // Bind the loaded root to the committed source selected by `root_kind`.
        // root_kind encoding:
        // - 0 => pub_inputs.trace_commitment
        // - 1 => pub_inputs.comp_commitment
        // - 2+i => pub_inputs.fri_commitments[i] for i in 0..MAX_FRI_LAYERS
        let rk = current[ROOT_KIND];
        // Enforce rk in {0..=1+MAX_FRI_LAYERS} on load_root rows.
        let mut rk_range = rk;
        for k in 1..=(1 + MAX_FRI_LAYERS as u64) {
            rk_range = rk_range * (rk - E::from(super::BaseElement::new(k)));
        }

        // Compute Lagrange selectors over points {0..=1+MAX_FRI_LAYERS}.
        let max_kind = 1 + MAX_FRI_LAYERS;
        let mut sels: Vec<E> = Vec::with_capacity(max_kind + 1);
        for k in 0..=max_kind {
            let mut num = E::ONE;
            let mut den = E::ONE;
            let k_fe = E::from(super::BaseElement::new(k as u64));
            for m in 0..=max_kind {
                if m == k {
                    continue;
                }
                let m_fe = E::from(super::BaseElement::new(m as u64));
                num *= rk - m_fe;
                den *= k_fe - m_fe;
            }
            sels.push(num * den.inv());
        }

        // Build expected root constants for each kind.
        let mut fri_roots: Vec<[E; 4]> = Vec::with_capacity(MAX_FRI_LAYERS);
        for i in 0..MAX_FRI_LAYERS {
            let root_i = if i < pub_inputs.fri_commitments.len() {
                pub_inputs.fri_commitments[i]
            } else {
                [super::BaseElement::ZERO; 4]
            };
            fri_roots.push([
                E::from(root_i[0]),
                E::from(root_i[1]),
                E::from(root_i[2]),
                E::from(root_i[3]),
            ]);
        }

        for j in 0..4 {
            let root_curr = current[ROOT_REG_START + j];
            let root_next = next[ROOT_REG_START + j];
            let copy_constraint = root_next - root_curr;
            let update_constraint = root_next - current[FRI_START + j];
            let copy_ok = E::ONE - is_load_root;
            // On load_root rows: require current fri[j] equals the selected public root.
            let mut expected = sels[0] * E::from(pub_inputs.trace_commitment[j])
                + sels[1] * E::from(pub_inputs.comp_commitment[j]);
            for i in 0..MAX_FRI_LAYERS {
                expected += sels[2 + i] * fri_roots[i][j];
            }
            let bind_loaded = current[FRI_START + j] - expected;

            result[idx] = copy_ok * copy_constraint
                + is_load_root * update_constraint
                + is_load_root * bind_loaded
                + if j == 0 { is_load_root * rk_range } else { E::ZERO };
            idx += 1;
        }
    }

    // --- 11. Root-kind selector constraints (1) ---
    //
    // root_kind is a small selector used only for binding LOAD_ROOT4 rows to public-input roots.
    // We allow it to change only on transitions INTO an Init(kind=LOAD_ROOT4) row; otherwise it must copy.
    {
        let rk_cur = current[ROOT_KIND];
        let rk_next = next[ROOT_KIND];
        let copy_constraint = rk_next - rk_cur;

        // Allow updates when the NEXT row is Init(kind=LOAD_ROOT4).
        let next_rc = next[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k11 = E::from(super::BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8));
        let inv24 = E::from(super::BaseElement::new(17678129733188976641u64)); // 24^{-1}
        let l12_next = (next_rc - k8) * (next_rc - k9) * (next_rc - k10) * (next_rc - k11) * inv24;
        let next_is_load_root = next_op.is_init * l12_next;
        let copy_ok = E::ONE - next_is_load_root;
        result[idx] = copy_ok * copy_constraint;
        idx += 1;
    }

    // --- 12. Carry/register constraints (8) ---
    //
    // carry[0] is the scratch MERKLE_IDX which is consumed by the Merkle microprogram.
    // Other carry columns currently copy (they are activated in later hardening steps).
    {
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k11 = E::from(super::BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));
        let k13 = E::from(super::BaseElement::new(INIT_KIND_LOAD_MERKLE_IDX));

        // Lagrange denominators over {8..=13}: denom11=12, denom13=120.
        let inv12 = E::from(super::BaseElement::new(12)).inv();
        let inv_neg120 = E::from(super::BaseElement::new(153722867245121536u64)); // (-120)^{-1}
        let inv120 = E::ZERO - inv_neg120;

        // l11 selector for init kind 11 over {8..=13}.
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * (rc - k13) * inv12;
        // l13 selector for init kind 13 over {8..=13}.
        let l13 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12) * inv120;

        // Root-mode selector: equals 1 only when aux[2]=0 (DeepCompose root check).
        let aux_mode = current[AUX_START + 2];
        let one = E::ONE;
        let two = E::from(super::BaseElement::new(2));
        let three = E::from(super::BaseElement::new(3));
        let four = E::from(super::BaseElement::new(4));
        let five = E::from(super::BaseElement::new(5));
        let six = E::from(super::BaseElement::new(6));
        // denom at aux_mode=0 is (-1)(-2)(-3)(-4)(-5)(-6) = 720.
        let inv_720 = E::from(super::BaseElement::new(720)).inv();
        let is_root_check = (aux_mode - one)
            * (aux_mode - two)
            * (aux_mode - three)
            * (aux_mode - four)
            * (aux_mode - five)
            * (aux_mode - six)
            * inv_720;

        for i in 0..8 {
            let c_cur = current[CARRY_START + i];
            let c_next = next[CARRY_START + i];
            let copy = c_next - c_cur;

            if i == 0 {
                // Load scratch Merkle idx from Q_IDX.
                let load = c_next - current[IDX_REG];
                // Store masked idx from QueryGen accumulator (fri[6]) on Nop(mode=15).
                let store_acc = c_next - current[FRI_START + 6];
                // Merkle idx update on init kind 11: idx_cur = 2*idx_next + dir.
                let dir = current[FRI_START + 5];
                let update = c_cur - (two * c_next + dir);
                // Root-mode requires the Merkle idx be fully consumed.
                let root_zero = op.is_deep * is_root_check * c_cur;

                let is_load = op.is_init * l13;
                let is_update = op.is_init * l11;
                let is_store = is_store_acc_nop;
                let copy_ok = E::ONE - is_load - is_update - is_store;
                result[idx] = copy_ok * copy
                    + is_load * load
                    + is_store * store_acc
                    + is_update * update
                    + root_zero;
            } else if i == 1 {
                // carry[1] holds the current FRI x-coordinate for this query.
                //
                // It is updated by:
                // - XExp init (mode 17): set to domain_offset.
                // - XExp step (mode 16): conditional multiply by base (bit from fri[5]).
                // - FriFold rows: x_{i+1} = x_i^2.
                let bit = current[FRI_START + 5];
                let base_cur = current[CARRY_START + 2];
                let xexp_mul = c_next - (c_cur * (E::ONE + bit * (base_cur - E::ONE)));
                // On FriFold rows, Winterfell updates the layer domain generator as g := g^2
                // while keeping the domain offset constant. This implies:
                //   x_next = offset * (g^2)^pos = (offset * g^pos)^2 / offset = x_cur^2 / offset.
                let inv_offset = E::from(super::BaseElement::GENERATOR).inv();
                let x_square = c_next - (c_cur * c_cur * inv_offset);

                let set_offset = c_next - E::from(super::BaseElement::GENERATOR);

                let allow_update = is_xexp_init_nop + is_xexp_step_nop + op.is_fri;
                let copy_ok = E::ONE - allow_update;
                result[idx] = copy_ok * copy
                    + is_xexp_init_nop * set_offset
                    + is_xexp_step_nop * xexp_mul
                    + op.is_fri * x_square;
            } else if i == 2 {
                // carry[2] holds the base for exponentiation (starts at g_lde and squares each step).
                let base_square = c_next - (c_cur * c_cur);
                // NOTE: g_lde depends on the *child* proof's LDE domain size (trace_len * blowup),
                // so it is not a single compile-time constant. We allow it to be set by the trace
                // builder on XExp init, and (for now) only constrain its squaring on XExp steps.
                //
                // TODO(security): bind this base to child proof parameters in-AIR (e.g. via a small
                // lookup table keyed by (trace_len, blowup) or by including g_lde in params_digest).
                let allow_update = is_xexp_init_nop + is_xexp_step_nop;
                let copy_ok = E::ONE - allow_update;
                result[idx] = copy_ok * copy + is_xexp_step_nop * base_square;
            } else if i == 6 {
                // carry[6] is the XExp step counter for the current query.
                //
                // - Reset to 0 on XExp init (mode 17).
                // - Increment by 1 on XExp step (mode 16).
                // - Must equal 32 on FriFold rows (ensures xexp ran to completion before folding).
                let reset = c_next; // == 0
                let inc = c_next - (c_cur + E::ONE);
                let thirty_two = E::from(super::BaseElement::new(32));
                let fri_requires_32 = op.is_fri * (c_cur - thirty_two);

                let allow_update = is_xexp_init_nop + is_xexp_step_nop;
                let copy_ok = E::ONE - allow_update;
                result[idx] = copy_ok * copy
                    + is_xexp_init_nop * reset
                    + is_xexp_step_nop * inc
                    + fri_requires_32;
            } else if i == 5 {
                // carry[5] is the per-query "upper-half" bit (msb of the transcript-derived Q_IDX).
                //
                // We capture it at the transition from the last QueryGen row (mode 6) to the first
                // Freeze row (mode 13) inside `decompose_fri4_u64_canonical(capture_bits=domain_bits)`.
                // This is exactly the highest captured bit and corresponds to "upper-half" for the LDE domain.
                // Detect next row is Freeze Nop (aux[2]=13).
                let next_mode = next[AUX_START + 2];
                let next_is_freeze = next_mode
                    * (next_mode - six)
                    * (next_mode - seven)
                    * (next_mode - eight)
                    * (next_mode - nine)
                    * (next_mode - ten)
                    * (next_mode - eleven)
                    * (next_mode - twelve)
                    * (next_mode - fourteen)
                    * (next_mode - fifteen)
                    * (next_mode - sixteen)
                    * (next_mode - seventeen)
                    * E::from(super::BaseElement::new(12320341145653937489u64)); // inv(1572480)
                let next_is_freeze_nop = next_op.is_nop * next_is_freeze;

                let capture_swap = is_qgen_nop * next_is_freeze_nop * (c_next - current[FRI_START + 5]);

                // On capture/capture-idx/xexp-init rows, clear swap bit to 0 (will be overwritten on the qgen→freeze boundary).
                let reset_swap = (is_capture_nop + is_capture_idx_nop + is_xexp_init_nop) * c_next;

                // Enforce binary always (defense-in-depth).
                let binary = c_cur * (c_cur - E::ONE);

                let allow_update = is_qgen_nop * next_is_freeze_nop + is_capture_nop + is_capture_idx_nop + is_xexp_init_nop;
                let copy_ok = E::ONE - allow_update;
                result[idx] = copy_ok * copy + capture_swap + reset_swap + binary;
            } else {
                // carry[3], carry[4] are reserved for DEEP accumulators:
                // - reset to 0 on root-check rows (DeepCompose mode 0),
                // - update on Nop(mode=7) rows as:
                //   next = cur + gamma * (Tx - Tz)   for carry[3]
                //   next = cur + gamma * (Tx - Tzg)  for carry[4]
                if i == 3 || i == 4 {
                    let is_root_row = op.is_deep * is_root_check;
                    let reset = c_next; // == 0
                    // DEEP-accumulate (Nop(mode=7)).
                    let tx = current[FRI_START + 0];
                    let tz = current[FRI_START + 1];
                    let tzg = current[FRI_START + 2];
                    let gamma = current[FRI_START + 3];
                    let delta = if i == 3 { tx - tz } else { tx - tzg };
                    let update_deep = c_next - (c_cur + gamma * delta);

                    // Terminal Horner (Nop(mode=18)).
                    // carry[3] = acc := acc*x + coeff, carry[4] = ctr := ctr+1
                    let x_term = current[CARRY_START + 1];
                    let coeff = current[FRI_START + 7];
                    let update_horner = if i == 3 {
                        c_next - (c_cur * x_term + coeff)
                    } else {
                        c_next - (c_cur + E::ONE)
                    };

                    let allow_update = is_root_row + is_deepacc_nop + is_horner_nop;
                    let copy_ok = E::ONE - allow_update;
                    result[idx] = copy_ok * copy
                        + is_root_row * reset
                        + is_deepacc_nop * update_deep
                        + is_horner_nop * update_horner;
                } else {
                    // carry[7] stores the previous layer's folded value for inter-layer linkage.
                    if i == 7 {
                        let set_on_fold = c_next - current[FRI_START + 4];
                        let allow_update = op.is_fri;
                        let copy_ok = E::ONE - allow_update;
                        result[idx] = copy_ok * copy + op.is_fri * set_on_fold;
                    } else {
                        result[idx] = copy;
                    }
                }
            }
            idx += 1;
        }
    }

    // --- 13. Auxiliary constraints (4) ---
    
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
        } else if i == 1 {
            // mode counter (aux[1])
            //
            // Tracks statement hash (mode 4) and params digest (mode 5) verifications.
            //
            // Packed encoding:
            //   aux[1] = statement_count
            //          + 4096 * params_count
            //          + 65536 * fri_link_count
            //          + 2^32 * root_count
            //
            // This prevents attacks where an attacker skips these critical bindings
            // or substitutes other check types.
            //
            // Update rules:
            // - On DeepCompose mode 0: aux[1] += 2^32 (increment root count)
            // - On DeepCompose mode 4: aux[1] += 1 (increment statement count)
            // - On DeepCompose mode 5: aux[1] += 4096 (increment params count)
            // - On DeepCompose mode 3: aux[1] += 65536 (increment FRI inter-layer link count)
            // - Otherwise: aux[1] unchanged (copy)
            //
            // We normalize polynomial selectors to 0/1 indicators.
            let mode = current[AUX_START + 2];
            let one = E::ONE;
            let two = E::from(super::BaseElement::new(2));
            let three = E::from(super::BaseElement::new(3));
            let four = E::from(super::BaseElement::new(4));
            let five = E::from(super::BaseElement::new(5));
            let six = E::from(super::BaseElement::new(6));
            
            // Raw selector for mode 4 (non-zero = 48 when mode=4; zero at mode=0..6 except 4):
            // mode_4_raw = mode*(mode-1)*(mode-2)*(mode-3)*(mode-5)*(mode-6)
            let mode_4_raw =
                mode * (mode - one) * (mode - two) * (mode - three) * (mode - five) * (mode - six);
            // Normalize: divide by 48 to get 1 when mode=4
            // 48^(-1) mod Goldilocks prime = 18062436901301780481
            let inv_48 = E::from(super::BaseElement::new(18062436901301780481u64));
            let is_mode_4 = mode_4_raw * inv_48;
            
            // Raw selector for mode 5 (non-zero = -120 when mode=5; zero at mode=0..6 except 5):
            // mode_5_raw = mode*(mode-1)*(mode-2)*(mode-3)*(mode-4)*(mode-6)
            let mode_5_raw =
                mode * (mode - one) * (mode - two) * (mode - three) * (mode - four) * (mode - six);
            // Normalize: divide by -120 to get 1 when mode=5
            // (-120)^(-1) mod Goldilocks prime = 153722867245121536
            let inv_neg_120 = E::from(super::BaseElement::new(153722867245121536u64));
            let is_mode_5 = mode_5_raw * inv_neg_120;

            // Selector for mode 0 (root check): equals 1 iff mode==0, else 0 on {1,2,3,4,5,6}.
            // denom at mode=0 is (-1)(-2)(-3)(-4)(-5)(-6) = 720.
            let inv_720 = E::from(super::BaseElement::new(720)).inv();
            let mode_0_raw =
                (mode - one) * (mode - two) * (mode - three) * (mode - four) * (mode - five) * (mode - six);
            let is_mode_0 = mode_0_raw * inv_720;

            // Selector for mode 6 (FRI inter-layer link check).
            // mode_6_raw = mode*(mode-1)*(mode-2)*(mode-3)*(mode-4)*(mode-5)
            // - equals 720 when mode=6
            // - equals 0 on {0,1,2,3,4,5}
            let mode_6_raw =
                mode * (mode - one) * (mode - two) * (mode - three) * (mode - four) * (mode - five);
            let is_mode_6 = mode_6_raw * inv_720;
            
            // Increment values
            let four_thousand_ninety_six = E::from(super::BaseElement::new(4096));
            let sixty_five_thousand_five_hundred_thirty_six = E::from(super::BaseElement::new(65536));
            let two_pow_32 = E::from(super::BaseElement::new(1u64 << 32));
            
            // Constraint:
            // aux[1]_next = aux[1]_curr
            //              + is_deep * (is_mode_0 * 2^32
            //                          + is_mode_4 * 1
            //                          + is_mode_5 * 4096
            //                          + is_mode_6 * 65536)
            let increment =
                op.is_deep * (is_mode_0 * two_pow_32
                    + is_mode_4
                    + is_mode_5 * four_thousand_ninety_six
                    + is_mode_6 * sixty_five_thousand_five_hundred_thirty_six);
            let mode_counter_constraint = aux_next - aux_curr - increment;
            
            result[idx] = mode_counter_constraint;
        } else if i == 3 {
            // Checkpoint counter (aux[3])
            // 
            // This counter MUST increment by exactly 1 on each DeepCompose operation.
            // The boundary constraint then ensures the final count equals expected.
            // This prevents attackers from skipping verification steps.
            //
            // Constraint: aux_next = aux_curr + is_deep
            // Equivalently: aux_next - aux_curr - is_deep = 0
            let checkpoint_constraint = aux_next - aux_curr - op.is_deep;
            result[idx] = checkpoint_constraint;
        } else {
            // aux[0]: round counter (handled above)
            // aux[2]: mode value.
            //
            // SECURITY: aux[2] is a mode tag:
            // - On Nop rows: restrict to {0,6,7,8,9,10,11,12,13,14,15,16,17,18}.
            // - On DeepCompose rows: restrict to {0,1,2,3,4,5}.
            let mode = aux_curr;
            let six = E::from(super::BaseElement::new(6));
            let seven = E::from(super::BaseElement::new(7));
            let eight = E::from(super::BaseElement::new(8));
            let nine = E::from(super::BaseElement::new(9));
            let ten = E::from(super::BaseElement::new(10));
            let eleven = E::from(super::BaseElement::new(11));
            let twelve = E::from(super::BaseElement::new(12));
            let thirteen = E::from(super::BaseElement::new(13));
            let fourteen = E::from(super::BaseElement::new(14));
            let fifteen = E::from(super::BaseElement::new(15));
            let sixteen = E::from(super::BaseElement::new(16));
            let seventeen = E::from(super::BaseElement::new(17));
            let eighteen = E::from(super::BaseElement::new(18));
            let in_set = mode
                * (mode - six)
                * (mode - seven)
                * (mode - eight)
                * (mode - nine)
                * (mode - ten)
                * (mode - eleven)
                * (mode - twelve)
                * (mode - thirteen)
                * (mode - fourteen)
                * (mode - fifteen)
                * (mode - sixteen)
                * (mode - seventeen)
                * (mode - eighteen); // = 0 iff mode ∈ {0,6,7,8,9,10,11,12,13,14,15,16,17,18}
            let one = E::ONE;
            let two = E::from(super::BaseElement::new(2));
            let three = E::from(super::BaseElement::new(3));
            let four = E::from(super::BaseElement::new(4));
            let five = E::from(super::BaseElement::new(5));
            let deep_in_set = mode
                * (mode - one)
                * (mode - two)
                * (mode - three)
                * (mode - four)
                * (mode - five)
                * (mode - E::from(super::BaseElement::new(6))); // = 0 iff mode ∈ {0,1,2,3,4,5,6}
            result[idx] = op.is_nop * in_set + op.is_deep * deep_in_set;
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
/// Compute ARK1 constants for the given round using Lagrange interpolation
fn compute_round_constants_lagrange<E: FieldElement<BaseField = super::BaseElement>>(
    round_counter: E,
) -> [E; HASH_STATE_WIDTH] {
    use winter_crypto::hashers::Rp64_256;
    
    let mut ark1 = [E::ZERO; HASH_STATE_WIDTH];
    
    // Precompute Lagrange basis denominators (these are constants)
    // L_r(x) = prod_{j!=r} (x - j) / (r - j)
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
    
    // For each state element, interpolate the ARK1 constant
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
            
            // Add contribution: ARK1[r][i] * L_r(round_counter)
            // Use Winterfell's ARK1 constants directly
            let ark1_val = E::from(Rp64_256::ARK1[r][i]);
            ark1[i] = ark1[i] + ark1_val * lagrange_basis;
        }
    }
    
    ark1
}

/// Compute the expected output of one RPO round
/// 
/// This MUST match Winterfell's Rp64_256 exactly.
/// - Forward S-box (x^7) for first 6 elements (indices 0-5)
/// - Inverse S-box (x^{1/7}) for last 6 elements (indices 6-11)
/// 
/// For constraint verification:
/// - Forward: we compute expected = sbox(temp) and verify next == expected
/// - Inverse: we need temp' such that sbox(temp') = temp, i.e., temp' = inv_sbox(temp)
///   But we can't compute inv_sbox in constraints. Instead, we verify sbox(next) = temp.
/// 
/// So we return what the pre-MDS state should look like BEFORE applying MDS,
/// and the constraint verifies the S-box relationship appropriately.
/// Compute the intermediate value after first half of RPO round: mid = MDS(sbox(current)) + ARK1
/// 
/// Winterfell round structure: sbox → MDS → +ARK1 → inv_sbox → MDS → +ARK2
/// We compute up to +ARK1, then verification is done separately.
fn compute_rpo_mid<E: FieldElement<BaseField = super::BaseElement>>(
    state: &[E; HASH_STATE_WIDTH],
    ark1: &[E; HASH_STATE_WIDTH],
    result: &mut [E; HASH_STATE_WIDTH],
) {
    use winter_crypto::hashers::Rp64_256;
    
    // Step 1: Apply S-box to all elements
    let mut after_sbox = [E::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        after_sbox[i] = sbox(state[i]);
    }

    // Step 2: Apply MDS matrix using Winterfell's constants
    let mut after_mds = [E::ZERO; HASH_STATE_WIDTH];
    for i in 0..HASH_STATE_WIDTH {
        after_mds[i] = E::ZERO;
        for j in 0..HASH_STATE_WIDTH {
            let mds_val = E::from(Rp64_256::MDS[i][j]);
            after_mds[i] = after_mds[i] + mds_val * after_sbox[j];
        }
    }

    // Step 3: Add ARK1 constants
    for i in 0..HASH_STATE_WIDTH {
        result[i] = after_mds[i] + ark1[i];
    }
}

/// Apply inverse MDS matrix to state
fn apply_inv_mds<E: FieldElement<BaseField = super::BaseElement>>(
    state: &[E; HASH_STATE_WIDTH],
    result: &mut [E; HASH_STATE_WIDTH],
) {
    use winter_crypto::hashers::Rp64_256;
    
    for i in 0..HASH_STATE_WIDTH {
        result[i] = E::ZERO;
        for j in 0..HASH_STATE_WIDTH {
            let inv_mds_val = E::from(Rp64_256::INV_MDS[i][j]);
            result[i] = result[i] + inv_mds_val * state[j];
        }
    }
}

/// Compute ARK2 constants for the given round using Lagrange interpolation
fn compute_ark2_lagrange<E: FieldElement<BaseField = super::BaseElement>>(
    round_counter: E,
) -> [E; HASH_STATE_WIDTH] {
    use winter_crypto::hashers::Rp64_256;
    
    let mut ark2 = [E::ZERO; HASH_STATE_WIDTH];
    
    // Use Lagrange interpolation to select the correct ARK2 for the round
    // For round r in 0..7, the Lagrange basis polynomial L_r(x) = prod_{j!=r}((x-j)/(r-j))
    for i in 0..HASH_STATE_WIDTH {
        for r in 0..7usize {
            let mut lagrange_coeff = E::ONE;
            for j in 0..7usize {
                if j != r {
                    let r_val = E::from(super::BaseElement::new(r as u64));
                    let j_val = E::from(super::BaseElement::new(j as u64));
                    let diff = r_val - j_val;
                    // Compute (round_counter - j) / (r - j)
                    lagrange_coeff = lagrange_coeff * (round_counter - j_val) * diff.inv();
                }
            }
            ark2[i] = ark2[i] + lagrange_coeff * E::from(Rp64_256::ARK2[r][i]);
        }
    }
    
    ark2
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
        // Verify indices are consistent with VERIFIER_TRACE_WIDTH (42)
        assert_eq!(SEL_0, 0);
        assert_eq!(SEL_1, 1);
        assert_eq!(SEL_2, 2);
        assert_eq!(HASH_STATE_START, 3);
        assert_eq!(HASH_STATE_END, 3 + 12);
        assert_eq!(FRI_START, 15);
        assert_eq!(FRI_END, 23);
        assert_eq!(IDX_REG, 23);
        assert_eq!(ROOT_REG_START, 24);
        assert_eq!(ROOT_REG_END, 28);
        assert_eq!(QGEN_CTR, 28);
        assert_eq!(ROOT_KIND, 29);
        assert_eq!(CARRY_START, 30);
        assert_eq!(CARRY_END, 38);
        assert_eq!(AUX_START, 38);
        assert_eq!(AUX_END, VERIFIER_TRACE_WIDTH);
    }

}
