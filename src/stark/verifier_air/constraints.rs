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

use winterfell::{math::FieldElement, EvaluationFrame};

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

/// Auxiliary column range
pub const AUX_START: usize = ROOT_KIND + 1;
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
        // We use 5 kinds (8,9,10,11,12) with degree-4 Lagrange basis polynomials.
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k11 = E::from(super::BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));

        // Ensure init kind is in {8,9,10,11,12} on Init rows:
        // (rc-8)(rc-9)(rc-10)(rc-11)(rc-12) = 0
        let init_kind_in_range = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12);

        // Lagrange basis over points {8,9,10,11,12}:
        // denom8  = (8-9)(8-10)(8-11)(8-12)     = 24
        // denom9  = (9-8)(9-10)(9-11)(9-12)     = -6
        // denom10 = (10-8)(10-9)(10-11)(10-12)  = 4
        // denom11 = (11-8)(11-9)(11-10)(11-12)  = -6
        // denom12 = (12-8)(12-9)(12-10)(12-11)  = 24
        let inv24 = E::from(super::BaseElement::new(17678129733188976641u64));
        let inv4 = E::from(super::BaseElement::new(13835058052060938241u64));
        let inv_neg6 = E::from(super::BaseElement::new(3074457344902430720u64)); // (-6)^{-1}

        let l8 = (rc - k9) * (rc - k10) * (rc - k11) * (rc - k12) * inv24;
        let l9 = (rc - k8) * (rc - k10) * (rc - k11) * (rc - k12) * inv_neg6;
        let l10 = (rc - k8) * (rc - k9) * (rc - k11) * (rc - k12) * inv4;
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * inv_neg6;
        let l12 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k11) * inv24;

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

        // Combine init constraints by kind selector.
        // Also enforce init kind range on ALL init rows by adding the cubic constraint once (i==0).
        let init_constraint =
            l8 * init_reset_constraint
                + l9 * init_load_constraint
                + l10 * init_copy_constraint
                + l11 * init_merkle_constraint
                + l12 * init_rootload_constraint
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

    // Nop sub-mode selectors.
    //
    // SECURITY: On Nop rows we restrict aux[2] to a small set of mode tags, and then use
    // Lagrange basis polynomials to activate different constraint sub-systems.
    //
    // Allowed Nop sub-modes: {0,6,8,9,10,11,12,13}
    // - 6  : QueryGen (bit/shift + accumulator)
    // - 8  : ZeroCheck (fri[4] == 0), used to bind terminal quotient = 0
    // - 9  : Canonicality check for Goldilocks u64 extraction (see below)
    // - 10 : PoWShift (QueryGen shift with bit forced to 0)
    // - 11 : Capture binding (fri[4] == hash_state[0]) to bind derived integers to transcript
    let seven = E::from(super::BaseElement::new(7));
    let eight = E::from(super::BaseElement::new(8));
    let nine = E::from(super::BaseElement::new(9));
    let ten = E::from(super::BaseElement::new(10));
    let eleven = E::from(super::BaseElement::new(11));

    // Denominator inverses for Lagrange basis over points {0,6,7,8,9,10,11,12,13}.
    //
    // NOTE: we keep the interpolation set (including 7) even though 7 is disallowed by the
    // "allowed Nop sub-modes" constraint below; the basis polynomials still evaluate to the
    // correct 0/1 indicators on the remaining allowed points, and this avoids re-deriving
    // constants.
    //
    // Precomputed in Goldilocks:
    // - inv(-30240), inv(-1920), inv(1296), inv(-1440), inv(2640), inv(-8640), inv(65520)
    let inv_neg_30240 = E::from(super::BaseElement::new(4978302855505701807u64));
    let inv_neg_1920 = E::from(super::BaseElement::new(9607679202820096u64));
    let inv_1296 = E::from(super::BaseElement::new(12966808524102381417u64));
    let inv_neg_1440 = E::from(super::BaseElement::new(12310639618546816342u64));
    let inv_2640 = E::from(super::BaseElement::new(13408826465608555800u64));
    let inv_neg_8640 = E::from(super::BaseElement::new(8200687959562664164u64));
    let inv_65520 = E::from(super::BaseElement::new(540282385061150600u64));

    let twelve = E::from(super::BaseElement::new(12));
    let thirteen = E::from(super::BaseElement::new(13));

    // L_6(x) over {0,6,7,8,9,10,11,12,13} has denom = -30240.
    let is_qgen = aux_mode
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * inv_neg_30240;
    // L_8(x) denom = -1920
    let is_zerocheck = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * inv_neg_1920;
    // L_9(x) denom = 1296
    let is_canon = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * inv_1296;
    // L_10(x) denom = -1440
    let is_powshift = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * inv_neg_1440;
    // L_11(x) denom = 2640
    let is_capture = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - twelve)
        * (aux_mode - thirteen)
        * inv_2640;
    // L_12(x) denom = -8640
    let is_export = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - thirteen)
        * inv_neg_8640;
    // L_13(x) denom = 65520
    let is_freeze = aux_mode
        * (aux_mode - six)
        * (aux_mode - seven)
        * (aux_mode - eight)
        * (aux_mode - nine)
        * (aux_mode - ten)
        * (aux_mode - eleven)
        * (aux_mode - twelve)
        * inv_65520;

    let is_qgen_nop = op.is_nop * is_qgen;
    let is_zerocheck_nop = op.is_nop * is_zerocheck;
    let is_canon_nop = op.is_nop * is_canon;
    let is_powshift_nop = op.is_nop * is_powshift;
    let is_capture_nop = op.is_nop * is_capture;
    let is_export_nop = op.is_nop * is_export;
    let is_freeze_nop = op.is_nop * is_freeze;

    for i in 0..8 {
        let fri_curr = current[FRI_START + i];
        let fri_next = next[FRI_START + i];
        let copy_constraint = fri_next - fri_curr;

        // Selector for Init-kind 11 (Merkle merge prep): l11 over {8,9,10,11,12}.
        // We recompute it here because we need it for fri-column semantics.
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));
        let inv_neg6 = E::from(super::BaseElement::new(3074457344902430720u64)); // (-6)^{-1}
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * inv_neg6;

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
                    - is_zerocheck_nop
                    - is_powshift_nop
                    - is_export_nop
                    - is_freeze_nop);
            let qgen_shift = fri_curr - (two * fri_next + current[FRI_START + 5]);
            let zerocheck_constraint = fri_curr; // enforce fri[4] == 0
            // Capture binding: fri[4] == hash_state[0]
            let capture_constraint = fri_curr - current_hash[0];
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
                + (is_qgen_nop + is_powshift_nop + is_freeze_nop) * qgen_shift
                + is_zerocheck_nop * zerocheck_constraint
                + is_capture_nop * capture_constraint
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
                    );
            let acc_update = fri_next - (fri_curr + current[FRI_START + 5] * current[FRI_START + 7]);
            let acc_copy = fri_next - fri_curr;
            // Capture mode anchors accumulator at 0.
            let capture_acc_zero = is_capture_nop * fri_curr;
            result[idx] = op.is_deep * equality_constraint
                + copy_ok * copy_constraint
                + (is_qgen_nop + is_powshift_nop) * acc_update
                + is_freeze_nop * acc_copy
                + capture_acc_zero
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
            
            result[idx] = op.is_deep * is_root_check * root_constraint
                + op.is_deep * is_statement_check * statement_constraint
                + op.is_deep * is_params_check * params_constraint
                + both_not_special * copy_constraint;
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
                        - is_zerocheck_nop
                        - is_canon_nop
                        - is_powshift_nop
                        - is_capture_nop
                        - is_export_nop
                        - is_freeze_nop);
                let qgen_bit = fri_curr * (fri_curr - one);

                result[idx] = copy_ok * copy_constraint
                    + op.is_init * l11 * enforce_binary(dir)
                    + is_qgen_nop * qgen_bit;
                // PoWShift: enforce bit==0
                result[idx] = result[idx] + is_powshift_nop * fri_curr;
                // Freeze mode uses fri[5] as the bit; enforce bit binary.
                result[idx] = result[idx] + is_freeze_nop * qgen_bit;
                // Canonicality mode does not impose any constraints on fri[5] here (fri[5] is used as inverse witness).
            } else {
                // i == 7: on QueryGen Nop rows, fri[7] is pow2 and doubles each step:
                //   pow2_next = 2 * pow2_cur.
                let copy_ok = both_not_special
                    * (one
                        - is_qgen_nop
                        - is_zerocheck_nop
                        - is_canon_nop
                        - is_powshift_nop
                        - is_export_nop
                        );
                let pow2_update = fri_next - (two * fri_curr);
                // Capture mode anchors pow2 at 1.
                let capture_pow2_one = is_capture_nop * (fri_curr - one);
                result[idx] = copy_ok * copy_constraint
                    + (is_qgen_nop + is_powshift_nop) * pow2_update
                    + capture_pow2_one;
            }
        }
        idx += 1;
    }

    // --- 8. Index register constraints (1) ---
    //
    // Dedicated Merkle index register semantics:
    // - Default: copy
    // - On Init kind 11: idx_cur = 2*idx_next + dir   (dir in fri[5])
    // - On DeepCompose root-check rows (aux[2]=0): idx must be 0
    // - On Export Nop rows (aux[2]=12): idx_next = fri[6] (accumulator)
    {
        let idx_curr = current[IDX_REG];
        let idx_next = next[IDX_REG];
        let copy_constraint = idx_next - idx_curr;

        // l11 selector for init kind 11 over {8,9,10,11,12}.
        let rc = current[ROUND_COUNTER];
        let k8 = E::from(super::BaseElement::new(INIT_KIND_RESET_WITH_LEN));
        let k9 = E::from(super::BaseElement::new(INIT_KIND_LOAD_CAPACITY4));
        let k10 = E::from(super::BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE));
        let k12 = E::from(super::BaseElement::new(INIT_KIND_LOAD_ROOT4));
        let inv_neg6 = E::from(super::BaseElement::new(3074457344902430720u64)); // (-6)^{-1}
        let l11 = (rc - k8) * (rc - k9) * (rc - k10) * (rc - k12) * inv_neg6;

        // Root-mode index must be fully consumed: idx == 0 after all Merkle steps.
        // is_root_check = Π_{k=1..6}(aux[2]-k) (non-zero only when aux[2]=0).
        let aux_mode = current[AUX_START + 2];
        let one = E::ONE;
        let two = E::from(super::BaseElement::new(2));
        let three = E::from(super::BaseElement::new(3));
        let four = E::from(super::BaseElement::new(4));
        let five = E::from(super::BaseElement::new(5));
        let six = E::from(super::BaseElement::new(6));
        let is_root_check = (aux_mode - one)
            * (aux_mode - two)
            * (aux_mode - three)
            * (aux_mode - four)
            * (aux_mode - five)
            * (aux_mode - six);
        let root_idx_zero = op.is_deep * is_root_check * idx_curr;

        // Merkle idx update on Init kind 11.
        let dir = current[FRI_START + 5];
        let idx_update_constraint = idx_curr - (two * idx_next + dir);
        let merkle_idx_update = op.is_init * l11 * idx_update_constraint;

        // Export: idx_next = acc (fri[6]) on aux[2]=12 Nop rows.
        let export_constraint = idx_next - current[FRI_START + 6];
        let export_term = is_export_nop * export_constraint;

        // CONTROL-FLOW HARDENING (export): require export rows are preceded by the terminal
        // ZeroCheck row (aux[2]=8), which ensures the decompose gadget ran to completion.
        // We enforce this by looking at the *next* row:
        //   if next row is export_nop, current row must be zerocheck_nop.
        let next_mode = next[AUX_START + 2];
        let next_is_export = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - eleven)
            * (next_mode - thirteen)
            * inv_neg_8640;
        let next_is_export_nop = next_op.is_nop * next_is_export;
        let export_requires_prev_zerocheck = next_is_export_nop * (E::ONE - is_zerocheck_nop);

        // Copy by default, except on init-kind 11 and export rows.
        let copy_ok = E::ONE - op.is_init * l11 - is_export_nop;
        result[idx] = copy_ok * copy_constraint
            + merkle_idx_update
            + root_idx_zero
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
        let other_mode = E::ONE - is_capture_nop - inc_mode;

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
            * inv_neg_8640;
        let next_is_export_nop = next_op.is_nop * next_is_export;
        let prev_export_requires_ctr = next_is_export_nop * (ctr_cur - sixty_four);

        // Allow the counter to reset at the start of a new microprogram: disable the "copy" constraint
        // on transitions INTO a capture row (aux[2]=11 on NEXT row).
        let next_is_capture = next_mode
            * (next_mode - six)
            * (next_mode - seven)
            * (next_mode - eight)
            * (next_mode - nine)
            * (next_mode - ten)
            * (next_mode - twelve)
            * (next_mode - thirteen)
            * inv_2640;
        let next_is_capture_nop = next_op.is_nop * next_is_capture;

        result[idx] = is_capture_nop * reset
            + inc_mode * inc
            + other_mode * (E::ONE - next_is_capture_nop) * copy
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

    // --- 12. Auxiliary constraints (4) ---
    
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

            // Raw selector for mode 0 (non-zero = -120 when mode=0; zero at mode=1..5):
            // mode_0_raw = (mode-1)(mode-2)(mode-3)(mode-4)(mode-5)
            let mode_0_raw =
                (mode - one) * (mode - two) * (mode - three) * (mode - four) * (mode - five);
            // Normalize: divide by -120 to get 1 when mode=0
            let is_mode_0 = mode_0_raw * inv_neg_120;

            // Selector for mode 3 (FRI inter-layer link check).
            // mode_3_raw = mode*(mode-1)*(mode-2)*(mode-4)*(mode-5)
            // - equals 12 when mode=3
            // - equals 0 on {0,1,2,4,5}
            let mode_3_raw =
                mode * (mode - one) * (mode - two) * (mode - four) * (mode - five);
            let inv_12 = E::from(super::BaseElement::new(12)).inv();
            let is_mode_3 = mode_3_raw * inv_12;
            
            // Increment values
            let four_thousand_ninety_six = E::from(super::BaseElement::new(4096));
            let sixty_five_thousand_five_hundred_thirty_six = E::from(super::BaseElement::new(65536));
            let two_pow_32 = E::from(super::BaseElement::new(1u64 << 32));
            
            // Constraint:
            // aux[1]_next = aux[1]_curr
            //              + is_deep * (is_mode_0 * 2^32
            //                          + is_mode_4 * 1
            //                          + is_mode_5 * 4096
            //                          + is_mode_3 * 65536)
            let increment =
                op.is_deep * (is_mode_0 * two_pow_32
                    + is_mode_4
                    + is_mode_5 * four_thousand_ninety_six
                    + is_mode_3 * sixty_five_thousand_five_hundred_thirty_six);
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
            // - On Nop rows: restrict to {0,6,8,9,10,11,12,13}.
            // - On DeepCompose rows: restrict to {0,1,2,3,4,5}.
            let mode = aux_curr;
            let six = E::from(super::BaseElement::new(6));
            let eight = E::from(super::BaseElement::new(8));
            let nine = E::from(super::BaseElement::new(9));
            let ten = E::from(super::BaseElement::new(10));
            let eleven = E::from(super::BaseElement::new(11));
            let twelve = E::from(super::BaseElement::new(12));
            let thirteen = E::from(super::BaseElement::new(13));
            let in_set = mode
                * (mode - six)
                * (mode - eight)
                * (mode - nine)
                * (mode - ten)
                * (mode - eleven)
                * (mode - twelve)
                * (mode - thirteen); // = 0 iff mode ∈ {0,6,8,9,10,11,12,13}
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
                * (mode - five); // = 0 iff mode ∈ {0,1,2,3,4,5}
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
        // Verify indices are consistent with VERIFIER_TRACE_WIDTH (34)
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
        assert_eq!(AUX_START, 30);
        assert_eq!(AUX_END, VERIFIER_TRACE_WIDTH);
    }

}
