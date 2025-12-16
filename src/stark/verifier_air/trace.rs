//! Trace Builder for Verifier AIR
//!
//! Builds the execution trace for verifying a STARK proof.
//! The trace is a sequential record of all operations the verifier performs.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, StarkField},
    TraceTable,
};

use super::{
    VerifierOp, HASH_STATE_WIDTH, NUM_SELECTORS, VERIFIER_TRACE_WIDTH,
};
use super::constraints::{
    AUX_START, CARRY_START, FRI_START, HASH_STATE_START, IDX_REG, QGEN_CTR, ROOT_KIND,
    ROOT_REG_START,
};

// Init kinds (encoded via aux[0] on Init rows).
// Must match `constraints.rs`.
const INIT_KIND_RESET_WITH_LEN: u64 = 8;
const INIT_KIND_LOAD_CAPACITY4: u64 = 9;
const INIT_KIND_COPY_DIGEST_FROM_RATE: u64 = 10;
const INIT_KIND_MERKLE_PREP_MERGE8: u64 = 11;
const INIT_KIND_LOAD_ROOT4: u64 = 12;
const INIT_KIND_LOAD_MERKLE_IDX: u64 = 13;

// ============================================================================
// TRACE BUILDER
// ============================================================================

/// Builds an execution trace for verifying a STARK proof
pub struct VerifierTraceBuilder {
    /// Current row index
    row: usize,
    /// Trace columns
    trace: Vec<Vec<BaseElement>>,
    /// Current hash state
    hash_state: [BaseElement; HASH_STATE_WIDTH],
    /// Current FRI working state
    fri_state: [BaseElement; 8],
    /// Dedicated Merkle index register (persists across hash plumbing ops).
    idx_reg: BaseElement,
    /// Expected-root register (4 elements): Merkle root digest being verified against.
    root_reg: [BaseElement; 4],
    /// QueryGen step counter (used to force the capture→64-step qgen→export microprogram in AIR).
    qgen_ctr: BaseElement,
    /// Root-kind selector (used to bind root_reg to the committed public-input roots).
    root_kind: BaseElement,
    /// Carry/register columns (8): cross-op binding.
    carry_state: [BaseElement; 8],
    /// Current auxiliary state
    /// aux[0]: round counter (0-6 during permute, 7 otherwise)
    /// aux[1]: reserved for flags
    /// aux[2]: verification mode (0=root, 1=ood, 2=terminal, 3=deep)
    /// aux[3]: checkpoint counter (SECURITY: must reach expected count)
    aux_state: [BaseElement; 4],
}

impl VerifierTraceBuilder {
    /// Evaluate VerifierAir periodic columns at an OOD point `z`.
    ///
    /// VerifierAir uses 8-cycle periodic columns (RPO round constants). Winterfell's verifier
    /// evaluates these columns at the OOD point, so any host-side evaluation of
    /// `constraints::evaluate_all()` on OOD frames MUST provide the periodic values at `z`.
    fn periodic_values_at_z(z: BaseElement, trace_len: usize) -> Vec<BaseElement> {
        use super::hash_chiplet;
        use winter_math::StarkField;

        let periodic_cols = hash_chiplet::get_periodic_column_values();
        if periodic_cols.is_empty() {
            return vec![];
        }
        assert_eq!(trace_len % 8, 0, "trace_len must be multiple of 8");
        let k = trace_len / 8;

        // Let x be the trace-domain variable, and y = x^k, which has order 8.
        // Periodic columns are degree<8 polynomials in y, given by values at y = g^(j*k).
        let y = z.exp(k as u64);
        let g = BaseElement::get_root_of_unity(trace_len.ilog2());
        let y_points: [BaseElement; 8] = [
            g.exp(0u64),
            g.exp(k as u64),
            g.exp((2 * k) as u64),
            g.exp((3 * k) as u64),
            g.exp((4 * k) as u64),
            g.exp((5 * k) as u64),
            g.exp((6 * k) as u64),
            g.exp((7 * k) as u64),
        ];

        let mut out = Vec::with_capacity(periodic_cols.len());
        for col in periodic_cols.iter() {
            debug_assert_eq!(col.len(), 8);
            // Lagrange interpolate Q(y) at `y` from 8 points.
            let mut acc = BaseElement::ZERO;
            for j in 0..8 {
                let mut num = BaseElement::ONE;
                let mut den = BaseElement::ONE;
                for m in 0..8 {
                    if m == j {
                        continue;
                    }
                    num *= y - y_points[m];
                    den *= y_points[j] - y_points[m];
                }
                let lj = num * den.inv();
                acc += col[j] * lj;
            }
            out.push(acc);
        }
        out
    }
    /// Create a new trace builder with estimated length
    pub fn new(estimated_length: usize) -> Self {
        let trace = (0..VERIFIER_TRACE_WIDTH)
            .map(|_| Vec::with_capacity(estimated_length))
            .collect();

        Self {
            row: 0,
            trace,
            hash_state: [BaseElement::ZERO; HASH_STATE_WIDTH],
            fri_state: [BaseElement::ZERO; 8],
            idx_reg: BaseElement::ZERO,
            root_reg: [BaseElement::ZERO; 4],
            qgen_ctr: BaseElement::ZERO,
            root_kind: BaseElement::ZERO,
            carry_state: [BaseElement::ZERO; 8],
            aux_state: [BaseElement::ZERO; 4],
        }
    }

    /// Emit a row to the trace
    /// 
    /// SECURITY: For DeepCompose operations, the checkpoint counter (aux[3])
    /// is incremented AFTER this row. The transition constraint will verify
    /// that the next row has checkpoint = current + 1.
    fn emit_row(&mut self, op: VerifierOp) {
        // Encode operation as selectors
        let (s0, s1, s2) = encode_op(op);

        // Write selector columns
        self.trace[0].push(s0);
        self.trace[1].push(s1);
        self.trace[2].push(s2);

        // Write hash state columns
        for i in 0..HASH_STATE_WIDTH {
            self.trace[HASH_STATE_START + i].push(self.hash_state[i]);
        }

        // Write FRI working columns
        for i in 0..8 {
            self.trace[FRI_START + i].push(self.fri_state[i]);
        }

        // Write idx register column
        self.trace[IDX_REG].push(self.idx_reg);

        // Write expected-root register columns
        for j in 0..4 {
            self.trace[ROOT_REG_START + j].push(self.root_reg[j]);
        }

        // Write qgen_ctr and root_kind columns
        self.trace[QGEN_CTR].push(self.qgen_ctr);
        self.trace[ROOT_KIND].push(self.root_kind);

        // Write carry columns
        for i in 0..8 {
            self.trace[CARRY_START + i].push(self.carry_state[i]);
        }

        // Write auxiliary columns
        for i in 0..4 {
            self.trace[AUX_START + i].push(self.aux_state[i]);
        }

        self.row += 1;
        
        // After DeepCompose operations, update counters
        // DeepCompose = 6, which means verification occurred at this step.
        if op == VerifierOp::DeepCompose {
            // Increment checkpoint counter
            // The transition constraint will enforce: next[aux[3]] = current[aux[3]] + 1
            self.aux_state[3] = self.aux_state[3] + BaseElement::ONE;
            
            // Update mode counter based on mode (aux[2])
            //
            // Packed encoding:
            // - statement_count contributes +1 (mode 4)
            // - params_count contributes +4096 (mode 5)
            // - root_count contributes +2^32 (mode 0)
            //
            // This prevents a prover from skipping specific binding steps.
            let mode = self.aux_state[2].as_int();
            if mode == 4 {
                self.aux_state[1] = self.aux_state[1] + BaseElement::ONE;
            } else if mode == 5 {
                self.aux_state[1] = self.aux_state[1] + BaseElement::new(4096);
            } else if mode == 0 {
                self.aux_state[1] = self.aux_state[1] + BaseElement::new(1u64 << 32);
            }
        }
    }

    /// Initialize the sponge state
    pub fn init_sponge(&mut self) {
        // Constrained reset: transition enforces next hash state is all zeros with len=0.
        self.reset_hash_with_len(0);
        // Reset scratch columns after emitting the init row.
        self.fri_state = [BaseElement::ZERO; 8];
    }

    /// Set the current FRI x-coordinate (stored in `carry[1]`).
    ///
    /// This is primarily a helper for tests; production code should derive x from `IDX_REG`.
    pub fn set_fri_x(&mut self, x: BaseElement) {
        self.carry_state[1] = x;
    }

    /// Constrained reset of the hash state to all-zeros with state[0] = len.
    ///
    /// Implemented as an Init row with aux[0]=INIT_KIND_RESET_WITH_LEN and fri[0]=len.
    /// The AIR transition constraints enforce the next row's hash state equals the reset state.
    fn reset_hash_with_len(&mut self, len: usize) {
        // Provide the length (domain separation) to the AIR via fri[0].
        self.fri_state = [BaseElement::ZERO; 8];
        self.fri_state[0] = BaseElement::new(len as u64);
        // aux[0] selects init kind on Init rows.
        self.aux_state[0] = BaseElement::new(INIT_KIND_RESET_WITH_LEN);
        self.emit_row(VerifierOp::Init);

        // Apply the reset for subsequent rows (this becomes the "next" hash state).
        self.hash_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.hash_state[0] = BaseElement::new(len as u64);

        // Reset aux[0] back to 7 (not in permute) for normal operations.
        self.aux_state[0] = BaseElement::new(7);
    }

    /// Constrained load of hash_state[0..3] from fri[0..3] (capacity load).
    /// Zeros the rest of the state.
    fn load_capacity4_from_fri(&mut self, cap: [BaseElement; 4]) {
        self.fri_state = [BaseElement::ZERO; 8];
        self.fri_state[0..4].copy_from_slice(&cap);
        self.aux_state[0] = BaseElement::new(INIT_KIND_LOAD_CAPACITY4);
        self.emit_row(VerifierOp::Init);

        self.hash_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.hash_state[0..4].copy_from_slice(&cap);
        self.aux_state[0] = BaseElement::new(7);
    }

    /// Constrained copy of digest from rate[0..3] (hash_state[4..7]) into capacity[0..3].
    /// Zeros the rest of the state.
    fn copy_digest_from_rate_to_capacity(&mut self) {
        self.fri_state = [BaseElement::ZERO; 8];
        self.aux_state[0] = BaseElement::new(INIT_KIND_COPY_DIGEST_FROM_RATE);
        self.emit_row(VerifierOp::Init);

        let digest = [
            self.hash_state[4],
            self.hash_state[5],
            self.hash_state[6],
            self.hash_state[7],
        ];
        self.hash_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.hash_state[0..4].copy_from_slice(&digest);
        self.aux_state[0] = BaseElement::new(7);
    }

    /// Absorb 8 elements into the sponge rate
    ///
    /// The row shows the state BEFORE absorption.
    /// The next row (typically Permute or Nop) shows the post-absorption state.
    pub fn absorb(&mut self, input: &[BaseElement; 8]) {
        // Provide absorbed block to the AIR via fri[0..7]. The dedicated Merkle index register
        // is now `idx_reg`, so there is no need to special-case any absorbed limb.
        self.fri_state = *input;
        // Keep aux[0]=7 (not in permute) on Absorb rows.
        self.aux_state[0] = BaseElement::new(7);
        
        // Emit row BEFORE modifying (shows pre-absorption state)
        self.emit_row(VerifierOp::Absorb);
        
        // XOR input into rate portion (elements 4-11)
        for i in 0..8 {
            self.hash_state[4 + i] = self.hash_state[4 + i] + input[i];
        }
    }

    /// Execute one RPO permutation (7 rounds + padding row)
    ///
    /// Each row shows the state BEFORE the operation is applied.
    /// The transition constraint verifies: next_state = RPO_round(current_state, round)
    /// The round number is stored in aux[0] for constraint verification.
    pub fn permute(&mut self) {
        for round in 0..super::RPO_ROUNDS {
            // Store round number in aux[0] for constraint verification
            self.aux_state[0] = BaseElement::new(round as u64);
            
            // Emit row BEFORE applying the round (shows pre-round state)
            self.emit_row(VerifierOp::Permute);
            
            // Then apply the round
            self.apply_rpo_round(round);
        }
        
        // Reset round counter for non-permute operations
        self.aux_state[0] = BaseElement::new(7); // 7 indicates "not in permute"
        // Padding Nop row must use a valid Nop sub-mode.
        self.aux_state[2] = BaseElement::ZERO;
        
        // Padding row for cycle alignment (shows final state after all rounds)
        self.emit_row(VerifierOp::Nop);
    }

    /// Apply one RPO round using Winterfell's implementation directly
    fn apply_rpo_round(&mut self, round: usize) {
        use winter_crypto::hashers::Rp64_256;
        // Use Winterfell's round function directly
        Rp64_256::apply_round(&mut self.hash_state, round);
    }

    /// Squeeze 4 elements from the sponge (capacity)
    pub fn squeeze(&mut self) -> [BaseElement; 4] {
        self.aux_state[0] = BaseElement::new(7); // Not in permute
        self.emit_row(VerifierOp::Squeeze);
        [
            self.hash_state[0],
            self.hash_state[1],
            self.hash_state[2],
            self.hash_state[3],
        ]
    }

    // ============================================================================
    // DEFAULT-RANDOM-COIN HELPERS (Winterfell-compatible)
    // ============================================================================
    //
    // Winterfell's DefaultRandomCoin is counter-based and uses Rp64_256 as:
    // - seed := hash_elements(context.to_elements() || pub_inputs.to_elements())
    // - reseed := merge(seed, digest)
    // - draw  := merge_with_int(seed, counter).first_limb (seed unchanged)
    //
    // We implement the required hash primitives using the already-constrained sponge ops:
    // reset_hash_with_len(len) + absorb(blocks) + permute() + copy_digest_from_rate_to_capacity().

    /// Constrained Rp64_256 hash of field elements, returning a 4-limb digest.
    ///
    /// This mirrors `Hasher::hash_elements(elements)` for BaseElement inputs.
    pub(crate) fn hash_elements_digest(&mut self, elements: &[BaseElement]) -> [BaseElement; 4] {
        let len = elements.len();
        self.reset_hash_with_len(len);

        for chunk in elements.chunks(8) {
            let mut block = [BaseElement::ZERO; 8];
            for (i, &e) in chunk.iter().enumerate() {
                block[i] = e;
            }
            self.absorb(&block);
            self.permute();
        }

        // `hash_elements` returns digest from rate[0..3] after permutation(s).
        self.copy_digest_from_rate_to_capacity();
        [self.hash_state[0], self.hash_state[1], self.hash_state[2], self.hash_state[3]]
    }

    /// Constrained `merge(seed, digest)` where both are 4-limb digests.
    pub(crate) fn merge_digest(&mut self, seed: [BaseElement; 4], digest: [BaseElement; 4]) -> [BaseElement; 4] {
        let mut block = [BaseElement::ZERO; 8];
        block[0..4].copy_from_slice(&seed);
        block[4..8].copy_from_slice(&digest);
        self.hash_elements_digest(&block)
    }

    /// Constrained `merge_with_int(seed, x)` as `hash_elements([seed0..3, x])`.
    pub(crate) fn merge_digest_with_int(&mut self, seed: [BaseElement; 4], x: u64) -> [BaseElement; 4] {
        let mut block = [BaseElement::ZERO; 5];
        block[0..4].copy_from_slice(&seed);
        block[4] = BaseElement::new(x);
        self.hash_elements_digest(&block)
    }

    /// Bind `fri[4] == hash_state[0]` on a dedicated Nop row (aux[2] = 11).
    ///
    /// This uses the existing capture constraint in `constraints.rs` and lets us
    /// “export” a transcript-derived u64 limb into the Merkle index register.
    pub(crate) fn capture_fri4_equals_hash0(&mut self) {
        self.fri_state[4] = self.hash_state[0];
        // Anchor QueryGen state for the subsequent decomposition block.
        // This prevents "pow2=0, acc=anything" bypasses.
        self.fri_state[6] = BaseElement::ZERO; // acc
        self.fri_state[7] = BaseElement::ONE;  // pow2
        self.qgen_ctr = BaseElement::ZERO;
        self.aux_state[2] = BaseElement::new(11);
        self.emit_row(VerifierOp::Nop);
        // Reset swap bit (carry[5]) *after* the capture row, so the AIR constraint
        // (which applies on the capture row) forces the NEXT row's carry[5] to be 0,
        // without violating copy constraints on the transition into this row.
        self.carry_state[5] = BaseElement::ZERO;
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Capture binding: fri[4] == IDX_REG (persistent query index).
    ///
    /// This starts a constrained QueryGen block which can derive masked indices/bits from Q_IDX
    /// without re-squeezing transcript state.
    pub(crate) fn capture_fri4_equals_idx_reg(&mut self) {
        self.fri_state[4] = self.idx_reg;
        self.fri_state[5] = BaseElement::ZERO; // bit placeholder
        self.fri_state[6] = BaseElement::ZERO; // acc
        self.fri_state[7] = BaseElement::ONE;  // pow2
        self.qgen_ctr = BaseElement::ZERO;
        self.aux_state[2] = BaseElement::new(14);
        self.emit_row(VerifierOp::Nop);
        // Reset swap bit after the capture-idx row (see comment in capture_fri4_equals_hash0).
        self.carry_state[5] = BaseElement::ZERO;
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Store QueryGen accumulator (fri[6]) into scratch Merkle index register carry[0].
    pub(crate) fn store_acc_to_merkle_idx(&mut self) {
        self.aux_state[2] = BaseElement::new(15);
        self.emit_row(VerifierOp::Nop);
        self.carry_state[0] = self.fri_state[6];
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Constrained masking: set `carry[0] := idx_reg mod 2^bits`.
    ///
    /// Implemented by:
    /// - capture idx_reg into fri[4] (mode 14),
    /// - run `bits` QueryGen steps to accumulate low bits into fri[6],
    /// - store accumulator into carry[0] (mode 15),
    /// after which the Merkle microprogram consumes carry[0] down to 0.
    pub fn mask_idx_reg_to_merkle_idx(&mut self, bits: usize) {
        self.capture_fri4_equals_idx_reg();
        for _ in 0..bits {
            let x_cur = self.fri_state[4].as_int();
            let bit = x_cur & 1;
            let x_next = x_cur >> 1;
            let acc_cur = self.fri_state[6];
            let pow2_cur = self.fri_state[7];
            let acc_next = if bit == 1 { acc_cur + pow2_cur } else { acc_cur };
            let pow2_next = pow2_cur + pow2_cur;
            self.aux_state[2] = BaseElement::new(6);
            self.fri_state[5] = BaseElement::new(bit);
            self.qgen_step(x_next, acc_next, pow2_next);
        }
        self.store_acc_to_merkle_idx();

        // Capture the layer swap bit (the next bit after masking low `bits`).
        //
        // We trigger the in-AIR carry[5] update on the qgen→freeze boundary:
        // current row: Nop(mode=6), next row: Nop(mode=13).
        let x_cur = self.fri_state[4].as_int();
        let bit = x_cur & 1;
        let x_next = x_cur >> 1;
        // Keep accumulator/pow2 consistent.
        let acc_cur = self.fri_state[6];
        let pow2_cur = self.fri_state[7];
        let acc_next = if bit == 1 { acc_cur + pow2_cur } else { acc_cur };
        let pow2_next = pow2_cur + pow2_cur;
        self.aux_state[2] = BaseElement::new(6);
        self.fri_state[5] = BaseElement::new(bit);
        self.qgen_step(x_next, acc_next, pow2_next);

        // Next row is Freeze: set carry[5] to the captured bit and emit a freeze step.
        self.carry_state[5] = BaseElement::new(bit);
        let x2_cur = self.fri_state[4].as_int();
        let bit2 = x2_cur & 1;
        let x2_next = x2_cur >> 1;
        let acc2_cur = self.fri_state[6];
        let pow2_2 = self.fri_state[7];
        // Freeze keeps accumulator constant and (per constraints) keeps pow2 constant.
        self.aux_state[2] = BaseElement::new(13);
        self.fri_state[5] = BaseElement::new(bit2);
        self.qgen_step(x2_next, acc2_cur, pow2_2);

        // Handoff row: exit Freeze mode cleanly.
        //
        // IMPORTANT: the Freeze constraint on fri[6]/fri[7] is a transition constraint, so it
        // constrains the *next emitted row*. We emit a neutral Nop row (aux[2]=0) to satisfy
        // the "acc/pow2 copied" expectation before moving on to the next microprogram
        // (e.g. MerklePath), which may reset scratch registers.
        self.aux_state[2] = BaseElement::ZERO;
        self.emit_row(VerifierOp::Nop);
    }

    /// Initialize the X exponentiation microprogram:
    /// - binds fri[4] = IDX_REG (Q_IDX)
    /// - sets carry_x = domain_offset, carry_base = g_lde
    /// - resets xexp counter carry[6] = 0
    pub fn xexp_init_from_qidx(&mut self) {
        self.fri_state[4] = self.idx_reg;
        self.fri_state[5] = BaseElement::ZERO;
        self.fri_state[6] = BaseElement::ZERO;
        self.fri_state[7] = BaseElement::ONE;

        self.carry_state[1] = BaseElement::GENERATOR; // domain_offset
        self.carry_state[2] = BaseElement::get_root_of_unity(6); // lde_domain_size=64
        self.carry_state[6] = BaseElement::ZERO; // xexp counter

        self.aux_state[2] = BaseElement::new(17);
        self.emit_row(VerifierOp::Nop);
        // Reset swap bit after the xexp-init row (AIR enforces next carry[5] == 0).
        self.carry_state[5] = BaseElement::ZERO;
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Run 32 XExp steps to compute x = domain_offset * g_lde^{IDX_REG}.
    pub fn xexp_run_32(&mut self) {
        for _ in 0..32 {
            let exp_cur = self.fri_state[4].as_int();
            let bit = exp_cur & 1;
            let exp_next = exp_cur >> 1;

            // Update carry_x and carry_base.
            let x = self.carry_state[1];
            let base = self.carry_state[2];
            if bit == 1 {
                self.carry_state[1] = x * base;
            }
            self.carry_state[2] = base * base;

            // Emit the constrained step row.
            self.aux_state[2] = BaseElement::new(16);
            self.fri_state[5] = BaseElement::new(bit);
            self.emit_row(VerifierOp::Nop);

            // Advance shift register and xexp counter for next row.
            self.fri_state[4] = BaseElement::new(exp_next);
            self.carry_state[6] = self.carry_state[6] + BaseElement::ONE;
        }
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Export the current accumulator in `fri[6]` into the *next row's* Merkle index register `idx_reg`.
    ///
    /// SECURITY: this is a cross-row binding enforced in AIR:
    /// on the export row (aux[2]=12): `next.idx_reg == cur.fri[6]`.
    pub(crate) fn export_fri6_to_next_idx_reg(&mut self) {
        let v = self.fri_state[6];
        self.aux_state[0] = BaseElement::new(7);
        self.aux_state[2] = BaseElement::new(12);
        self.emit_row(VerifierOp::Nop);
        // Prepare next row to actually carry the index.
        self.idx_reg = v;
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Fully decompose the current `fri[4]` (which must already be bound to the transcript via `capture_fri4_equals_hash0`)
    /// into a canonical 64-bit integer, while optionally:
    /// - enforcing PoW trailing-zero condition on the lowest `pow_zero_bits` bits (<= 32), and
    /// - returning the low `capture_bits` bits (<= 32) as a `u32` (for query positions).
    ///
    /// SECURITY:
    /// - We range-bind by shifting out *all 64 bits* and enforcing terminal quotient == 0 (mode 8).
    /// - We enforce Goldilocks canonicality via a dedicated check row (mode 9) using the (hi32,low32) limbs.
    /// - PoW: for the first `pow_zero_bits` steps, we use mode 10 which forces `bit==0` in-circuit.
    pub fn decompose_fri4_u64_canonical(
        &mut self,
        pow_zero_bits: usize,
        capture_bits: usize,
    ) -> u32 {
        assert!(pow_zero_bits <= 32, "pow_zero_bits must be <= 32");
        assert!(capture_bits <= 32, "capture_bits must be <= 32");

        // Phase A: shift out 32 bits to obtain hi32, while accumulating the low `capture_bits` bits.
        //
        // We use three Nop sub-modes:
        // - aux[2]=10 (PoWShift): shift with bit forced to 0 (for pow_zero_bits)
        // - aux[2]=6  (QueryGen): shift + accumulate (for capture_bits)
        // - aux[2]=13 (Freeze):   shift but keep accumulator constant (after capture_bits)
        let mut x_cur = self.fri_state[4].as_int();
        self.aux_state[0] = BaseElement::new(7);
        self.fri_state[6] = BaseElement::ZERO; // acc (masked low bits)
        // Always start pow2 at 1 and satisfy the enforced pow2 doubling constraints.
        self.fri_state[7] = BaseElement::ONE;

        let mut captured: u32 = 0;
        let mut acc_u64: u64 = 0;
        let mut pow2_u64: u64 = 1;

        for i in 0..32 {
            let bit = x_cur & 1;
            let x_next = x_cur >> 1;

            // Host-side tracking of the masked accumulator.
            if i < capture_bits {
                if bit == 1 {
                    acc_u64 = acc_u64.wrapping_add(pow2_u64);
                }
                pow2_u64 = pow2_u64.wrapping_mul(2);
                if i + 1 == capture_bits {
                    captured = acc_u64 as u32;
                }
            }

            // Witness for in-trace accumulator/pow2.
            let acc_cur = self.fri_state[6];
            let pow2_cur = self.fri_state[7];
            let (acc_next, pow2_next, mode) = if i < pow_zero_bits {
                // PoW shift: bit must be 0 (enforced by constraints). Keep acc unchanged.
                // pow2 still must follow doubling constraints.
                (acc_cur, pow2_cur + pow2_cur, BaseElement::new(10))
            } else if i < capture_bits {
                // Accumulate the first `capture_bits` bits.
                let acc_next = if bit == 1 { acc_cur + pow2_cur } else { acc_cur };
                let pow2_next = pow2_cur + pow2_cur;
                (acc_next, pow2_next, BaseElement::new(6))
        } else {
                // Freeze accumulator for remaining shifts.
                (acc_cur, pow2_cur, BaseElement::new(13))
            };

            self.aux_state[2] = mode;
            self.fri_state[5] = BaseElement::new(bit);
            self.qgen_step(x_next, acc_next, pow2_next);
            x_cur = x_next;

            // IMPORTANT (soundness): capture the per-query "upper-half" bit into carry[5]
            // exactly at the qgen→freeze boundary which AIR constrains:
            // current row: Nop(mode=6), next row: Nop(mode=13) and next.carry[5] == cur.fri[5].
            if capture_bits > 0 && i + 1 == capture_bits {
                self.carry_state[5] = BaseElement::new(bit);
            }
        }

        // After 32 shifts:
        // - fri[4] is now hi32 (as field element)
        // - fri[6] is the masked accumulator (pos)
        let hi32_u64 = self.fri_state[4].as_int();

        // Canonicality check row (mode 9): enforce hi32 != 0xFFFF_FFFF by requiring an inverse witness.
        let all_ones = 0xFFFF_FFFFu64;
        let diff = BaseElement::new(hi32_u64) - BaseElement::new(all_ones);
        let w = if diff == BaseElement::ZERO { BaseElement::ZERO } else { diff.inv() };
        self.aux_state[2] = BaseElement::new(9);
        // Keep fri[4]=hi32 and fri[6]=acc intact; fri[5] carries the inverse witness.
        self.fri_state[4] = BaseElement::new(hi32_u64);
        self.fri_state[5] = w;
        self.emit_row(VerifierOp::Nop);

        // Phase B: range-bind hi32 by shifting 32 more times; keep accumulator constant by setting pow2=0.
        self.aux_state[2] = BaseElement::new(6);
        self.fri_state[7] = BaseElement::ZERO; // pow2=0 => acc_update keeps acc unchanged
        let mut hi_cur = hi32_u64;
        for _ in 0..32 {
            let bit = hi_cur & 1;
            let hi_next = hi_cur >> 1;
            self.fri_state[5] = BaseElement::new(bit);
            self.qgen_step(hi_next, self.fri_state[6], BaseElement::ZERO);
            hi_cur = hi_next;
        }

        // Terminal quotient must be zero (mode 8): fri[4] == 0.
        self.aux_state[2] = BaseElement::new(8);
        self.fri_state[4] = BaseElement::new(self.fri_state[4].as_int());
        self.emit_row(VerifierOp::Nop);

        self.aux_state[2] = BaseElement::ZERO;
        captured
    }

    // ============================================================================
    // QUERY-GENERATION BIT GADGETS (aux[2] = 6 on Nop rows)
    // ============================================================================

    /// Start a QueryGen block for bit/shift arithmetic.
    ///
    /// Layout (current row values shown to constraints):
    /// - fri[4] = x (shift register)
    /// - fri[5] = bit (LSB of x)
    /// - fri[6] = acc
    /// - fri[7] = pow2
    ///
    /// Constraints (on Nop rows with aux[2]=6) enforce:
    /// - x_cur = 2*x_next + bit_cur
    /// - bit binary
    /// - acc_next = acc_cur + bit_cur * pow2_cur
    /// - pow2_next = 2 * pow2_cur
    fn qgen_begin(&mut self, x: u64) {
        self.aux_state[0] = BaseElement::new(7);
        self.aux_state[2] = BaseElement::new(6);
        self.fri_state[4] = BaseElement::new(x);
        self.fri_state[5] = BaseElement::new(x & 1);
        self.fri_state[6] = BaseElement::ZERO; // acc
        self.fri_state[7] = BaseElement::ONE;  // pow2
    }

    /// Advance one QueryGen step by emitting a Nop row and updating the registers to the next state.
    fn qgen_step(&mut self, x_next: u64, acc_next: BaseElement, pow2_next: BaseElement) {
        // Caller must set fri[5] for the current row (bit).
        self.emit_row(VerifierOp::Nop);

        // Count qgen micro-steps (used by AIR to force capture→64-step qgen→export).
        let mode = self.aux_state[2].as_int();
        if mode == 6 || mode == 10 || mode == 13 {
            self.qgen_ctr = self.qgen_ctr + BaseElement::ONE;
        }

        // Update registers for next row.
        self.fri_state[4] = BaseElement::new(x_next);
        self.fri_state[6] = acc_next;
        self.fri_state[7] = pow2_next;
        // fri[5] will be set from the new x on the next step.
    }

    /// Enforce PoW/grinding: low `g` bits of `x` are zero, by repeatedly shifting with bit=0.
    pub fn qgen_enforce_trailing_zeros(&mut self, x: u64, g: usize) {
        self.qgen_begin(x);
        for _ in 0..g {
            // Require bit=0 by choosing x_next = x_cur >> 1 and letting the constraint fail if odd.
            let x_cur = self.fri_state[4].as_int();
            let x_next = x_cur >> 1;
            let acc_next = self.fri_state[6];
            let pow2_next = self.fri_state[7] + self.fri_state[7]; // *2
            // Force bit=0 in witness for this step.
            self.fri_state[5] = BaseElement::ZERO;
            self.qgen_step(x_next, acc_next, pow2_next);
        }
        // Handoff row: make the final qgen step's `next` values explicit.
        // (Transition constraints reference `fri_next`.)
        self.aux_state[2] = BaseElement::ZERO;
        self.emit_row(VerifierOp::Nop);
    }

    /// Mask `x` to the low `bits` bits by extracting bits via shift, and accumulating.
    /// Returns the masked value as a BaseElement.
    pub fn qgen_mask_low_bits(&mut self, x: u64, bits: usize) -> BaseElement {
        self.qgen_begin(x);
        for _ in 0..bits {
            let x_cur = self.fri_state[4].as_int();
            let bit = x_cur & 1;
            let x_next = x_cur >> 1;
            let acc_cur = self.fri_state[6];
            let pow2_cur = self.fri_state[7];
            let acc_next = if bit == 1 { acc_cur + pow2_cur } else { acc_cur };
            let pow2_next = pow2_cur + pow2_cur;
            self.fri_state[5] = BaseElement::new(bit);
            self.qgen_step(x_next, acc_next, pow2_next);
        }
        let out = self.fri_state[6];
        // Same handoff row rationale as above: expose final `next` values.
        self.aux_state[2] = BaseElement::ZERO;
        self.emit_row(VerifierOp::Nop);
        out
    }

    /// Enforce that `x` fits in 32 bits (i.e. x < 2^32), by shifting out 32 bits and
    /// then asserting the remaining high part is zero.
    ///
    /// This avoids Winterfell's `merge_with_int` branch for `value >= MODULUS` and ensures
    /// `pow_nonce` is an actual integer knob rather than an arbitrary field element.
    pub fn qgen_assert_u32(&mut self, x: u64) {
        // Shift-right 32 times using QueryGen gadget (aux[2]=6).
        self.qgen_begin(x);
        for _ in 0..32 {
            let x_cur = self.fri_state[4].as_int();
            let bit = x_cur & 1;
            let x_next = x_cur >> 1;
            // Must satisfy the QueryGen accumulator constraints even if we don't use it.
            let acc_cur = self.fri_state[6];
            let pow2_cur = self.fri_state[7];
            let acc_next = if bit == 1 { acc_cur + pow2_cur } else { acc_cur };
            let pow2_next = pow2_cur + pow2_cur;
            self.fri_state[5] = BaseElement::new(bit);
            self.qgen_step(x_next, acc_next, pow2_next);
        }

        // Now fri[4] == x >> 32. Enforce it is zero on a dedicated Nop row (aux[2]=8).
        self.aux_state[0] = BaseElement::new(7);
        self.aux_state[2] = BaseElement::new(8);
        self.fri_state[4] = BaseElement::new(self.fri_state[4].as_int()); // keep current value
        self.emit_row(VerifierOp::Nop);

        // Return to default.
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Verify a single Merkle path step
    /// 
    /// Matches Winterfell's merge function: parent = hash_elements(left || right)
    /// Output is from rate portion (indices 4-7), copied to capacity (0-3) for next step.
    pub fn set_merkle_index(&mut self, idx: usize) {
        // In locked recursion, IDX_REG holds the persistent query index (Q_IDX).
        self.idx_reg = BaseElement::new(idx as u64);
    }

    /// Load the scratch Merkle index (MERKLE_IDX) from the persistent `idx_reg` (Q_IDX).
    ///
    /// Implemented as Init(kind=LOAD_MERKLE_IDX), which updates `carry[0]` in-circuit while
    /// keeping hash state unchanged.
    pub fn load_merkle_idx_from_qidx(&mut self) {
        // aux[0] selects init kind on Init rows.
        self.aux_state[0] = BaseElement::new(INIT_KIND_LOAD_MERKLE_IDX);
        self.emit_row(VerifierOp::Init);

        // Apply the constrained update for subsequent rows.
        self.carry_state[0] = self.idx_reg;

        self.aux_state[0] = BaseElement::new(7);
    }

    /// Merkle path step using the current index in `idx_reg`.
    ///
    /// This enforces direction bits are consistent with the index:
    /// dir = idx & 1; idx_next = idx >> 1.
    pub fn merkle_step_from_index(&mut self, sibling: [BaseElement; 4]) {
        // Current digest must be in capacity[0..3].
        let current_digest = [self.hash_state[0], self.hash_state[1], self.hash_state[2], self.hash_state[3]];

        let idx_u64 = self.carry_state[0].as_int();
        let dir_bit_u64 = idx_u64 & 1;
        let idx_next_u64 = idx_u64 >> 1;

        // Place sibling and dir into the current row, and use Init-kind 11 to constrain
        // the next row hash state to the reset+loaded merge state.
        self.fri_state[0..4].copy_from_slice(&sibling);
        self.fri_state[5] = BaseElement::new(dir_bit_u64);
        self.aux_state[0] = BaseElement::new(INIT_KIND_MERKLE_PREP_MERGE8);
        self.emit_row(VerifierOp::Init);

        // Apply constrained next state: reset to len=8 and load [left||right] into rate.
        self.hash_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.hash_state[0] = BaseElement::new(8);
        if dir_bit_u64 == 1 {
            // Current is right child: left=sibling, right=current_digest.
            for i in 0..4 {
                self.hash_state[4 + i] = sibling[i];
                self.hash_state[8 + i] = current_digest[i];
            }
        } else {
            // Current is left child: left=current_digest, right=sibling.
            for i in 0..4 {
                self.hash_state[4 + i] = current_digest[i];
                self.hash_state[8 + i] = sibling[i];
            }
        }

        // Update scratch index for next level (this is constrained by Init-kind 11 via carry[0] transition).
        self.carry_state[0] = BaseElement::new(idx_next_u64);

        // Reset aux[0] back to 7 for normal operations.
        self.aux_state[0] = BaseElement::new(7);

        // Permute to compute the merge hash.
        self.permute();
        
        // `hash_elements` output digest is in rate[0..3] after permutation.
        self.copy_digest_from_rate_to_capacity();
    }

    /// Perform FRI folding step.
    ///
    /// `x` must be the transcript-bound layer point. We take it from `carry[1]` so the caller
    /// cannot accidentally (or maliciously) inject a host-computed `x`.
    pub fn fri_fold(&mut self, f_x: BaseElement, f_neg_x: BaseElement, beta: BaseElement) -> BaseElement {
        // Store inputs
        self.fri_state[0] = f_x;
        self.fri_state[1] = f_neg_x;
        let x = self.carry_state[1];
        self.fri_state[2] = x;
        self.fri_state[3] = beta;

        // Compute folded value: g(x^2) = (f(x) + f(-x))/2 + beta * (f(x) - f(-x))/(2x)
        let two = BaseElement::new(2u64);
        let sum = f_x + f_neg_x;
        let diff = f_x - f_neg_x;
        let g = sum / two + beta * diff / (two * x);

        self.fri_state[4] = g;
        self.emit_row(VerifierOp::FriFold);

        // Advance x for the next layer: x_{i+1} = x_i^2.
        self.carry_state[1] = x * x;
        // Store folded value for inter-layer linkage checks.
        self.carry_state[7] = g;

        g
    }

    /// Verify FRI terminal condition
    /// 
    /// This verifies that the final folded value matches the remainder polynomial
    /// or is constant (depending on terminal mode).
    /// 
    /// For Constant terminal: all final values must be equal
    /// For Poly terminal: final_value == P(x) where P is the remainder polynomial
    /// 
    /// Parameters:
    /// - final_value: The final folded value for this query
    /// - expected_value: The expected value (either first value for constant, or P(x))
    /// - is_constant_mode: True if using constant terminal (all values equal)
    /// 
    /// Returns true if verification passes.
    pub fn verify_fri_terminal_poly(
        &mut self,
        final_value: BaseElement,
        c0: BaseElement,
        c1: BaseElement,
    ) -> bool {
        // Row layout:
        // fri[0]=final_value, fri[1]=c0, fri[2]=c1, carry[1]=x_terminal (already in-trace).
        self.fri_state[0] = final_value;
        self.fri_state[1] = c0;
        self.fri_state[2] = c1;

        // Witness lhs/rhs into fri[6..7]; AIR recomputes and constrains them.
        let x_term = self.carry_state[1];
        let expected = c0 + c1 * x_term;
        self.fri_state[6] = final_value;
        self.fri_state[7] = expected;

        self.aux_state[2] = BaseElement::new(2u64);
        self.emit_row(VerifierOp::DeepCompose);

        final_value == expected
    }

    /// Accumulate one DEEP term into carry[3] and carry[4] (t1_num and t2_num).
    ///
    /// - carry[3] += gamma * (T(x) - T(z))
    /// - carry[4] += gamma * (T(x) - T(zg))
    ///
    /// Implemented as a Nop row with aux[2]=7 (DEEP accumulate).
    pub fn deep_accumulate(&mut self, tx: BaseElement, tz: BaseElement, tzg: BaseElement, gamma: BaseElement) {
        self.aux_state[2] = BaseElement::new(7);
        self.fri_state[0] = tx;
        self.fri_state[1] = tz;
        self.fri_state[2] = tzg;
        self.fri_state[3] = gamma;
        // Keep equality lanes consistent on Nop rows.
        self.fri_state[6] = BaseElement::ZERO;
        self.fri_state[7] = BaseElement::ZERO;
        self.emit_row(VerifierOp::Nop);

        // Mirror the constrained next-state updates in builder state.
        self.carry_state[3] = self.carry_state[3] + gamma * (tx - tz);
        self.carry_state[4] = self.carry_state[4] + gamma * (tx - tzg);

        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Final DEEP check: enforce prover's layer-0 value equals computed DEEP(x).
    ///
    /// This emits a DeepCompose row (aux[2]=3). The AIR will enforce:
    /// - fri[6] == selected_f * (x-z)*(x-zg)
    /// - fri[7] == carry[3]*(x-zg) + carry[4]*(x-z)
    /// - fri[6] == fri[7]
    pub fn deep_check(&mut self, z: BaseElement, f_x: BaseElement, f_neg_x: BaseElement, g_trace: BaseElement) {
        // Layout for DEEP check row:
        // fri[0]=z, fri[1]=f_x, fri[2]=f_neg_x
        self.fri_state[0] = z;
        self.fri_state[1] = f_x;
        self.fri_state[2] = f_neg_x;

        // Provide witness values for the DEEP equation check; AIR recomputes and constrains them.
        // (We still compute them here to keep the trace builder honest and for debug sanity.)
        let x = self.carry_state[1];
        let zg = z * g_trace;
        let den_z = x - z;
        let den_zg = x - zg;
        let denom = den_z * den_zg;
        let b = self.carry_state[5];
        let selected = (BaseElement::ONE - b) * f_x + b * f_neg_x;
        self.fri_state[6] = selected * denom;
        self.fri_state[7] = self.carry_state[3] * den_zg + self.carry_state[4] * den_z;

        self.aux_state[2] = BaseElement::new(3);
        self.emit_row(VerifierOp::DeepCompose);
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Verify FRI inter-layer linkage:
    /// the previous layer's folded value (stored in carry[7]) must equal the next layer's opened value
    /// at the correct conjugate, selected by the transcript-derived swap bit carry[5].
    pub fn verify_fri_link(&mut self, next_f_x: BaseElement, next_f_neg_x: BaseElement) {
        // Provide the opened pair as inputs.
        self.fri_state[0] = next_f_x;
        self.fri_state[1] = next_f_neg_x;
        // Witness the selected value into fri[7]; AIR will recompute and constrain it.
        let b = self.carry_state[5];
        self.fri_state[6] = self.carry_state[7];
        self.fri_state[7] = (BaseElement::ONE - b) * next_f_x + b * next_f_neg_x;

        self.aux_state[2] = BaseElement::new(6);
        self.emit_row(VerifierOp::DeepCompose);
        self.aux_state[2] = BaseElement::ZERO;
    }

    /// Verify statement hash binding
    /// 
    /// This verifies that the statement hash computed from the proof data
    /// matches the expected statement hash from public inputs.
    /// 
    /// The statement hash binds all commitments (trace, comp, FRI) together.
    /// Without this check, an attacker could verify a DIFFERENT proof than
    /// what's claimed in the public inputs.
    /// 
    /// Parameters:
    /// - expected_hash: The expected statement hash from public inputs
    /// 
    /// Returns true if current hash_state[0..3] equals expected_hash.
    /// 
    /// Must be called AFTER absorbing all commitments into the sponge.
    /// The AIR constraint will verify hash_state[0..3] == pub_inputs.statement_hash.
    pub fn verify_statement_hash(&mut self, expected_hash: [BaseElement; 4]) -> bool {
        // The current hash_state[0..3] should contain the computed statement hash
        // (result of absorbing context + all commitments + permuting)
        
        let local_ok = self.hash_state[0] == expected_hash[0]
            && self.hash_state[1] == expected_hash[1]
            && self.hash_state[2] == expected_hash[2]
            && self.hash_state[3] == expected_hash[3];
        
        // Set mode = STATEMENT VERIFICATION (aux[2] = 4)
        // The AIR constraint will enforce: hash_state[0..3] == pub_inputs.statement_hash
        // This is the ONLY place we bind to public inputs, ensuring the prover
        // can't substitute fake commitments.
        self.aux_state[2] = BaseElement::new(4u64);
        // Equality constraint on DeepCompose is unconditional; keep fri[6..7] equal here.
        self.fri_state[6] = BaseElement::ZERO;
        self.fri_state[7] = BaseElement::ZERO;
        
        // Emit DeepCompose row - checkpoint counter increments
        self.emit_row(VerifierOp::DeepCompose);
        
        local_ok
    }

    /// Verify security-parameter digest binding (num_queries/blowup/grinding/folding/trace_len).
    /// 
    /// The AIR constraint will verify hash_state[0..3] == pub_inputs.params_digest when aux[2]=5.
    pub fn verify_params_digest(&mut self, params_digest: [BaseElement; 4]) -> bool {
        // Constrained load: move the computed digest into hash_state[0..3].
        // This is modeled as an Init(kind=LOAD_CAPACITY4) transition to avoid
        // any "out of band" hash_state mutation between rows.
        self.load_capacity4_from_fri(params_digest);
        
        // Set mode = PARAMS VERIFICATION (aux[2] = 5)
        self.aux_state[2] = BaseElement::new(5u64);
        // Equality constraint on DeepCompose is unconditional; keep fri[6..7] equal here.
        self.fri_state[6] = BaseElement::ZERO;
        self.fri_state[7] = BaseElement::ZERO;
        self.emit_row(VerifierOp::DeepCompose);
        true
    }

    /// Constrained load of the expected Merkle root digest into `root_reg`.
    ///
    /// This must be called before verifying Merkle paths for a commitment tree.
    /// It is implemented via Init(kind=LOAD_ROOT4), which updates `root_reg`
    /// from `fri[0..3]` in the transition constraints, while leaving `hash_state`
    /// unchanged (copy).
    pub fn set_expected_root(&mut self, expected_root: [BaseElement; 4]) {
        self.fri_state = [BaseElement::ZERO; 8];
        self.fri_state[0..4].copy_from_slice(&expected_root);
        self.aux_state[0] = BaseElement::new(INIT_KIND_LOAD_ROOT4);
        self.emit_row(VerifierOp::Init);

        // Apply the root_reg update for subsequent rows.
        self.root_reg = expected_root;

        // Reset aux[0] back to 7 (not in permute) for normal operations.
        self.aux_state[0] = BaseElement::new(7);
    }

    /// Load expected root for the trace commitment tree.
    pub fn set_expected_root_trace(&mut self, expected_root: [BaseElement; 4]) {
        self.root_kind = BaseElement::ZERO; // 0 = trace
        self.set_expected_root(expected_root);
    }

    /// Load expected root for the composition commitment tree.
    pub fn set_expected_root_comp(&mut self, expected_root: [BaseElement; 4]) {
        self.root_kind = BaseElement::ONE; // 1 = comp
        self.set_expected_root(expected_root);
    }

    /// Load expected root for an arbitrary `root_kind` slot.
    ///
    /// `root_kind` encoding is enforced in AIR on `LOAD_ROOT4` rows:
    /// - 0 => pub_inputs.trace_commitment
    /// - 1 => pub_inputs.comp_commitment
    /// - 2+i => pub_inputs.fri_commitments[i]
    pub fn set_expected_root_kind(&mut self, root_kind: u64, expected_root: [BaseElement; 4]) {
        self.root_kind = BaseElement::new(root_kind);
        self.set_expected_root(expected_root);
    }

    /// Load expected root for a specific FRI layer commitment tree.
    pub fn set_expected_root_fri(&mut self, layer_idx: usize, expected_root: [BaseElement; 4]) {
        self.root_kind = BaseElement::new((2 + layer_idx) as u64);
        self.set_expected_root(expected_root);
    }

    // NOTE: DEEP verification is implemented via `deep_accumulate()` + `deep_check()` to avoid
    // any host-computed expected values.

    /// Verify an equality `a == b` using the unconditional DeepCompose equality constraint
    /// (fri[6] == fri[7]) without affecting the mode counter.
    ///
    /// This is used for internal consistency checks (e.g. FRI inter-layer linkage).
    pub fn verify_eq(&mut self, a: BaseElement, b: BaseElement) -> bool {
        self.fri_state[6] = a;
        self.fri_state[7] = b;
        // Use a non-root/statement/params/DEEP mode to avoid triggering other gated checks.
        self.aux_state[2] = BaseElement::new(6u64);
        self.emit_row(VerifierOp::DeepCompose);
        a == b
    }
    
    /// Verify OOD constraint equation with explicit child AIR type
    ///
    /// This version allows specifying the child AIR type for recursive verification.
    /// Different child types have different constraints that need to be evaluated.
    ///
    /// # Child Types
    ///
    /// - `VerifierAir`: Verifier/Aggregator constraints (recursive verification)
    /// - `Generic`: Formula-as-witness for app proofs (VDF, Fib, Bitcoin, etc.)
    pub fn verify_ood_constraints_typed(
        &mut self,
        ood_frame: &super::ood_eval::OodFrame,
        z: BaseElement,
        g_trace: BaseElement,
        trace_len: usize,
        constraint_coeffs: &Vec<BaseElement>,
        pub_result: BaseElement,
        child_type: super::ood_eval::ChildAirType,
    ) -> bool {
        use super::ood_eval::{OodParams, verify_ood_constraint_equation_typed, evaluate_child_constraints};

        // Domain values
        let z_pow_n = z.exp((trace_len as u64).into());
        let g_pow_n_minus_1 = g_trace.exp(((trace_len - 1) as u64).into());
        let exemption = z - g_pow_n_minus_1;
        let zerofier_num = z_pow_n - BaseElement::ONE;
        let exemption_sq = exemption * exemption;

        // Combine C(z) from all composition columns: Σ C_i(z) * z^(i*n)
        let mut c_combined = BaseElement::ZERO;
        let mut z_pow_in = BaseElement::ONE;
        for &c_i in ood_frame.composition.iter() {
            c_combined += c_i * z_pow_in;
            z_pow_in *= z_pow_n;
        }

        // Transition constraints (child-type-specific evaluator; for Generic this interprets the formula).
        let constraints = evaluate_child_constraints(
            &ood_frame.trace_current,
            &ood_frame.trace_next,
            &child_type,
        );
        
        // Combine constraints with coefficients.
        let mut transition_sum = BaseElement::ZERO;
        for (i, c) in constraints.iter().enumerate() {
            if i < constraint_coeffs.len() {
                transition_sum = transition_sum + constraint_coeffs[i] * *c;
            }
        }

        // Boundary constraint:
        // - VerifierAir children use aux[3] as the boundary column (checkpoint counter).
        // - Generic/app children use col 1 (standard result column in app AIRs in this repo).
        let boundary_col = if matches!(child_type, super::ood_eval::ChildAirType::VerifierAir) {
            super::constraints::AUX_START + 3
        } else {
            1
        };
        // Boundary constraint numerator evaluation: f(z) - b(z).
        // Divisor for the single last-step boundary is (z - g^(n-1)).
        let boundary_value = ood_frame.trace_current.get(boundary_col)
            .copied()
            .unwrap_or(BaseElement::ZERO) - pub_result;
        let num_constraints = child_type.num_constraints();
        let boundary_coeff = constraint_coeffs.get(num_constraints)
            .copied()
            .unwrap_or(BaseElement::ZERO);
        let boundary_sum = boundary_coeff * boundary_value;

        // LHS/RHS (multiply-through form used by this verifier trace schedule)
        let lhs = transition_sum * exemption_sq + boundary_sum * zerofier_num;
        let rhs = c_combined * zerofier_num * exemption;

        // Store witness into fri[6], fri[7] and enforce equality with the DeepCompose equality constraint.
        self.fri_state[6] = lhs;
        self.fri_state[7] = rhs;
        self.aux_state[2] = BaseElement::ONE; // OOD mode
        self.emit_row(VerifierOp::DeepCompose);

        // Host-side consistency checker.
        let params = OodParams { z, trace_len, g_trace, constraint_coeffs: constraint_coeffs.clone(), pub_result };
        verify_ood_constraint_equation_typed(ood_frame, &params, &child_type).is_ok()
    }

    /// OOD verification for a VerifierAir *child proof*.
    ///
    /// VerifierAir has multiple boundary assertions (row 0 and final row) whose values depend on
    /// the child's public inputs. When verifying a VerifierAir proof recursively, we must use the
    /// full multiply-through equation (matching `ood_eval_r1cs`) rather than the simplified single-boundary form.
    pub fn verify_ood_constraints_verifier_air_child(
        &mut self,
        ood_frame: &super::ood_eval::OodFrame,
        z: BaseElement,
        g_trace: BaseElement,
        trace_len: usize,
        constraint_coeffs: &Vec<BaseElement>,
        trace_commitment: [BaseElement; 4],
        comp_commitment: [BaseElement; 4],
        fri_commitments: &Vec<[BaseElement; 4]>,
        num_queries: usize,
        proof_trace_len: usize,
        pub_result: BaseElement,
        expected_checkpoint_count: usize,
        expected_mode_counter: usize,
        statement_hash: &[BaseElement; 4],
        params_digest: &[BaseElement; 4],
    ) -> bool {
        // Domain values
        let z_pow_n = z.exp((trace_len as u64).into());
        let g_pow_n_minus_1 = g_trace.exp(((trace_len - 1) as u64).into());
        let exemption = z - g_pow_n_minus_1;
        let zerofier_num = z_pow_n - BaseElement::ONE;
        let z_minus_1 = z - BaseElement::ONE;

        // VerifierAir transition constraints evaluated with *child* public inputs.
        // We must supply these so statement/params/root checks are evaluated correctly at OOD.
        use super::constraints::evaluate_all;
        use super::VerifierPublicInputs;
        use winterfell::EvaluationFrame;

        let frame = EvaluationFrame::from_rows(
            ood_frame.trace_current.clone(),
            ood_frame.trace_next.clone(),
        );
        let pub_inputs = VerifierPublicInputs {
            statement_hash: *statement_hash,
            trace_commitment,
            comp_commitment,
            fri_commitments: fri_commitments.clone(),
            num_queries,
            proof_trace_len,
            g_trace,
            pub_result,
            expected_checkpoint_count: expected_checkpoint_count,
            params_digest: *params_digest,
            expected_mode_counter: expected_mode_counter,
        };
        // VerifierAir constraints depend on periodic columns (RPO round constants).
        // Provide the periodic values evaluated at the OOD point `z`.
        let periodic_values = Self::periodic_values_at_z(z, trace_len);
        let mut constraints = vec![BaseElement::ZERO; super::VERIFIER_TRACE_WIDTH];
        evaluate_all(&frame, &periodic_values, &mut constraints, &pub_inputs);

        if constraint_coeffs.len() < super::VERIFIER_TRACE_WIDTH + 8 || constraints.len() < super::VERIFIER_TRACE_WIDTH {
            return false;
        }

        let mut transition_sum = BaseElement::ZERO;
        for i in 0..super::VERIFIER_TRACE_WIDTH {
            transition_sum += constraint_coeffs[i] * constraints[i];
        }

        // Combine C(z) from all composition columns: Σ C_i(z) * z^(i*n)
        let mut c_combined = BaseElement::ZERO;
        let mut z_pow_in = BaseElement::ONE;
        for &c_i in ood_frame.composition.iter() {
            c_combined += c_i * z_pow_in;
            z_pow_in *= z_pow_n;
        }

        // Boundary contributions (match `ood_eval_r1cs`)
        let mut initial_sum = BaseElement::ZERO;
        // capacity[0..3] at columns 3..6 are zero at row 0
        for j in 0..4 {
            let col = 3 + j;
            initial_sum += constraint_coeffs[super::VERIFIER_TRACE_WIDTH + j] * ood_frame.trace_current[col];
        }
        // aux[1] initial = 0 (AUX_START+1)
        initial_sum += constraint_coeffs[super::VERIFIER_TRACE_WIDTH + 4]
            * ood_frame.trace_current[super::constraints::AUX_START + 1];
        // aux[3] initial = 0 (AUX_START+3)
        initial_sum += constraint_coeffs[super::VERIFIER_TRACE_WIDTH + 5]
            * ood_frame.trace_current[super::constraints::AUX_START + 3];

        let expected_mode = BaseElement::new(expected_mode_counter as u64);
        let expected_ckpt = BaseElement::new(expected_checkpoint_count as u64);
        let final_aux1 = ood_frame.trace_current[super::constraints::AUX_START + 1] - expected_mode;
        let final_aux3 = ood_frame.trace_current[super::constraints::AUX_START + 3] - expected_ckpt;
        let final_term =
            constraint_coeffs[super::VERIFIER_TRACE_WIDTH + 6] * final_aux1
                + constraint_coeffs[super::VERIFIER_TRACE_WIDTH + 7] * final_aux3;

        // Multiply-through equation:
        // transition_sum * exemption^2 * (z-1) + initial_sum * (z^n-1) * exemption + final_term * (z^n-1) * (z-1)
        //   = C(z) * (z^n-1) * (z-1) * exemption
        let exemption_sq = exemption * exemption;
        let lhs = transition_sum * exemption_sq * z_minus_1
            + initial_sum * zerofier_num * exemption
            + final_term * zerofier_num * z_minus_1;
        let rhs = c_combined * zerofier_num * z_minus_1 * exemption;

        // Store for AIR equality check in OOD mode.
        self.fri_state[6] = lhs;
        self.fri_state[7] = rhs;
        self.aux_state[2] = BaseElement::ONE; // OOD mode
        self.emit_row(VerifierOp::DeepCompose);

        lhs == rhs
    }

    /// Check that computed Merkle root matches expected commitment (local check only)
    /// 
    /// Returns true if hash_state[0..3] == expected_root, false otherwise.
    pub fn check_root(&self, expected_root: &[BaseElement; 4]) -> bool {
        self.hash_state[0] == expected_root[0]
            && self.hash_state[1] == expected_root[1]
            && self.hash_state[2] == expected_root[2]
            && self.hash_state[3] == expected_root[3]
    }
    
    /// Verify Merkle root in AIR (enforced by transition constraints)
    /// 
    /// This emits a DeepCompose row that the AIR constraint verifies:
    /// hash_state[0..3] == root_reg[0..3]
    /// 
    /// The expected root is stored in root_reg, computed root is in hash_state.
    /// Mode aux[2]=0 tells the AIR to check root verification.
    /// 
    /// Returns true if local check passes (AIR constraint will also enforce).
    pub fn verify_root(&mut self) -> bool {
        // Equality constraint on DeepCompose is unconditional; keep fri[6..7] equal here.
        self.fri_state[6] = BaseElement::ZERO;
        self.fri_state[7] = BaseElement::ZERO;
        
        // Set mode = ROOT VERIFICATION (aux[2] = 0)
        self.aux_state[2] = BaseElement::ZERO;
        
        // Emit DeepCompose row - AIR will verify hash_state[0..3] == root_reg[0..3]
        self.emit_row(VerifierOp::DeepCompose);

        // Reset DEEP accumulators after any root-check row (AIR enforces next carry[3..4] == 0).
        self.carry_state[3] = BaseElement::ZERO;
        self.carry_state[4] = BaseElement::ZERO;
        
        // Return local check result for caller to track
        self.check_root(&self.root_reg)
    }
    
    /// Get current hash state
    pub fn get_hash_state(&self) -> &[BaseElement; HASH_STATE_WIDTH] {
        &self.hash_state
    }

    /// Initialize hash state for a new Merkle path verification
    /// 
    /// Before starting a new Merkle path, the hash state should contain
    /// the leaf digest. This function hashes all leaf data using RPO sponge
    /// construction matching Winterfell's `hash_elements`:
    /// - state[0] = input length (domain separation)
    /// - Absorb elements into rate portion (state[4..12])
    /// - Permute after each block of 8 elements
    /// - OUTPUT is from rate portion (indices 4-7), copied to capacity (0-3)
    ///   for subsequent merkle_step operations
    pub fn init_leaf(&mut self, leaf_data: &[BaseElement]) {
        // Reset sponge with domain-separation length.
        self.reset_hash_with_len(leaf_data.len());
        
        // Absorb leaf data in 8-element blocks (rate width).
        // This matches `hash_elements` behavior.
        for chunk in leaf_data.chunks(8) {
            let mut block = [BaseElement::ZERO; 8];
            for (i, &e) in chunk.iter().enumerate() {
                block[i] = e;
            }
            self.absorb(&block);
                self.permute();
        }

        if leaf_data.is_empty() {
            // `hash_elements([])` still performs a permutation of the empty-block sponge.
            let block = [BaseElement::ZERO; 8];
            self.absorb(&block);
            self.permute();
        }
        
        // Output digest lives in rate[0..3] after permutation.
        self.copy_digest_from_rate_to_capacity();
    }

    /// Set the final acceptance flag
    pub fn accept(&mut self, _accepted: bool) {
        // Reset aux[0] to 7 before Accept row
        // Accept encodes the same as Nop (111), and Nop constraints require aux[0] = 7
        // After Merkle steps or other ops, aux[0] may be a direction bit (0 or 1)
        self.aux_state[0] = BaseElement::new(7);
        self.aux_state[2] = BaseElement::ZERO;
        
        // NOTE: We no longer set aux_state[3] here.
        // aux_state[3] is now the checkpoint counter, NOT the acceptance flag.
        // The acceptance is implicit: if checkpoint count reaches expected AND
        // all verification constraints passed, the proof is valid.
        
        self.emit_row(VerifierOp::Accept);
    }

    /// Pad trace to power of 2 and finalize
    pub fn finalize(mut self) -> TraceTable<BaseElement> {
        // Ensure trace length is power of 2
        let current_len = self.row;
        let target_len = current_len.next_power_of_two().max(8);

        // Reset aux[0] to 7 for Nop padding
        // Nop constraints require aux[0] = 7, but previous ops may have set it differently
        self.aux_state[0] = BaseElement::new(7);
        // Nop padding must use a valid Nop sub-mode.
        self.aux_state[2] = BaseElement::ZERO;

        // Pad with Nop rows
        while self.row < target_len {
            self.emit_row(VerifierOp::Nop);
        }

        // Convert to TraceTable
        TraceTable::init(self.trace)
    }

    /// Get current row count
    pub fn len(&self) -> usize {
        self.row
    }
}

/// Encode operation as 3 selector bits
///
/// Encoding:
/// ```text
/// s2 s1 s0 | Op value | Operation
/// ---------|----------|----------
///  0  0  0 |    0     | Init
///  0  0  1 |    1     | Absorb
///  0  1  0 |    2     | Permute
///  0  1  1 |    3     | Squeeze
///  1  0  0 |    4     | MerklePath
///  1  0  1 |    5     | FriFold
///  1  1  0 |    6     | DeepCompose
///  1  1  1 |    7+    | Nop/Accept
/// ```
fn encode_op(op: VerifierOp) -> (BaseElement, BaseElement, BaseElement) {
    let code = (op as u8).min(7); // Clamp to 3 bits
    let s0 = BaseElement::from((code >> 0) & 1); // bit 0 (LSB)
    let s1 = BaseElement::from((code >> 1) & 1); // bit 1
    let s2 = BaseElement::from((code >> 2) & 1); // bit 2 (MSB)
    (s0, s1, s2)
}


// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::verifier_air::VerifierPublicInputs;
    use crate::stark::verifier_air::ood_eval::ChildAirType;

    #[test]
    fn test_trace_builder_basic() {
        let mut builder = VerifierTraceBuilder::new(64);

        builder.init_sponge();
        builder.absorb(&[BaseElement::ONE; 8]);
        builder.permute();
        let _digest = builder.squeeze();

        assert_eq!(builder.len(), 1 + 1 + 8 + 1); // init + absorb + 7 permute + 1 nop + squeeze

        let trace = builder.finalize();
        // TraceTable length is always power of 2 after finalize
        // Use winterfell::Trace trait
        use winterfell::Trace;
        assert!(trace.length().is_power_of_two());
    }

    #[test]
    fn test_full_trace_generation() {
        let _pub_inputs = VerifierPublicInputs {
            statement_hash: [BaseElement::new(1); 4],
            trace_commitment: [BaseElement::new(2); 4],
            comp_commitment: [BaseElement::new(3); 4],
            fri_commitments: vec![[BaseElement::new(4); 4]; 2],
            num_queries: 2,
            proof_trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64), // 2^61 in Goldilocks
            pub_result: BaseElement::new(42),
            expected_checkpoint_count: VerifierPublicInputs::compute_expected_checkpoints(2, 2),
            params_digest: [BaseElement::ZERO; 4],
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1, 2, 2),
        };

        // We don't have a real Proof here, but we can test the trace building logic
        // by calling build_verifier_trace with a mock (would need adjustments)
    }

    #[test]
    fn test_ood_constraint_verification() {
        let mut builder = VerifierTraceBuilder::new(64);
        builder.init_sponge();

        // Create a valid OOD frame where transition constraints are satisfied
        // VDF: next0 = curr0^3 + curr1, next1 = curr0
        let curr0 = BaseElement::new(2);
        let curr1 = BaseElement::new(3);
        let next0 = BaseElement::new(11); // 2^3 + 3 = 11
        let next1 = BaseElement::new(2);  // = curr0

        let ood_frame = super::super::ood_eval::OodFrame::new(
            vec![curr0, curr1],
            vec![next0, next1],
            vec![BaseElement::ZERO, BaseElement::ZERO],
            vec![BaseElement::ZERO, BaseElement::ZERO],
        );

        let z = BaseElement::new(12345);
        let g_trace = BaseElement::new(2); // Simple generator
        let trace_len = 8;
        let constraint_coeffs = [
            BaseElement::ZERO, // alpha_0
            BaseElement::ZERO, // alpha_1
            BaseElement::ZERO, // beta_0
        ];
        let pub_result = curr1; // Match to avoid boundary term

        // Should pass because constraints are zero with zero coefficients
        let result = builder.verify_ood_constraints_typed(
            &ood_frame,
            z,
            g_trace,
            trace_len,
            &constraint_coeffs.to_vec(),
            pub_result,
            ChildAirType::generic_vdf(),
        );
        assert!(result, "OOD constraint verification should pass for valid transition");
    }

    #[test]
    fn test_op_encoding() {
        // Init = 0 = 0b000
        let (s0, s1, s2) = encode_op(VerifierOp::Init);
        assert_eq!(s0, BaseElement::ZERO); // bit 0
        assert_eq!(s1, BaseElement::ZERO); // bit 1
        assert_eq!(s2, BaseElement::ZERO); // bit 2

        // Permute = 2 = 0b010 -> s0=0, s1=1, s2=0
        let (s0, s1, s2) = encode_op(VerifierOp::Permute);
        assert_eq!(s0, BaseElement::ZERO);
        assert_eq!(s1, BaseElement::ONE);
        assert_eq!(s2, BaseElement::ZERO);

        // FriFold = 5 = 0b101 -> s0=1, s1=0, s2=1
        let (s0, s1, s2) = encode_op(VerifierOp::FriFold);
        assert_eq!(s0, BaseElement::ONE);
        assert_eq!(s1, BaseElement::ZERO);
        assert_eq!(s2, BaseElement::ONE);

        // Accept = 9, clamped to 7 = 0b111 -> s0=1, s1=1, s2=1 (treated as Nop)
        let (s0, s1, s2) = encode_op(VerifierOp::Accept);
        assert_eq!(s0, BaseElement::ONE);
        assert_eq!(s1, BaseElement::ONE);
        assert_eq!(s2, BaseElement::ONE);

        // Nop = 15, clamped to 7 = 0b111
        let (s0, s1, s2) = encode_op(VerifierOp::Nop);
        assert_eq!(s0, BaseElement::ONE);
        assert_eq!(s1, BaseElement::ONE);
        assert_eq!(s2, BaseElement::ONE);
    }
    
    /// Test that our hash matches Winterfell's Rp64_256
    #[test]
    fn test_hash_matches_winterfell() {
        use winter_crypto::hashers::Rp64_256;
        use winter_crypto::{Digest, ElementHasher};
        
        // Test hash_elements with various inputs
        let test_inputs: Vec<Vec<BaseElement>> = vec![
            vec![BaseElement::new(1), BaseElement::new(2)],
            vec![BaseElement::new(42)],
            (0..8).map(|i| BaseElement::new(i)).collect(),
            (0..16).map(|i| BaseElement::new(i * 7)).collect(),
        ];
        
        for input in test_inputs {
            // Compute with Winterfell
            let winterfell_digest = Rp64_256::hash_elements(&input);
            let digest_bytes = winterfell_digest.as_bytes();
            
            // Extract as 4 GL values (8 bytes each, LE)
            let mut winterfell_arr = [BaseElement::ZERO; 4];
            for i in 0..4 {
                let chunk = &digest_bytes[i * 8..(i + 1) * 8];
                let val = u64::from_le_bytes(chunk.try_into().unwrap());
                winterfell_arr[i] = BaseElement::new(val);
            }
            
            // Compute with our implementation
            let mut builder = VerifierTraceBuilder::new(256);
            builder.init_leaf(&input);
            let our_digest = [
                builder.hash_state[0],
                builder.hash_state[1],
                builder.hash_state[2],
                builder.hash_state[3],
            ];
            
            assert_eq!(
                our_digest, winterfell_arr,
                "Hash mismatch for input len {}: our {:?} vs winterfell {:?}",
                input.len(), our_digest, winterfell_arr
            );
        }
    }
    
    /// Test that our merge matches Winterfell's merge
    #[test]
    fn test_merge_matches_winterfell() {
        use winter_crypto::hashers::Rp64_256;
        use winter_crypto::{Digest, ElementHasher, Hasher};
        
        // First hash two inputs to get digests
        let left_input = vec![BaseElement::new(1), BaseElement::new(2), BaseElement::new(3), BaseElement::new(4)];
        let right_input = vec![BaseElement::new(5), BaseElement::new(6), BaseElement::new(7), BaseElement::new(8)];
        
        let left_digest = Rp64_256::hash_elements(&left_input);
        let right_digest = Rp64_256::hash_elements(&right_input);
        
        // Merge with Winterfell
        let winterfell_result = Rp64_256::merge(&[left_digest, right_digest]);
        let result_bytes = winterfell_result.as_bytes();
        
        let mut winterfell_arr = [BaseElement::ZERO; 4];
        for i in 0..4 {
            let chunk = &result_bytes[i * 8..(i + 1) * 8];
            let val = u64::from_le_bytes(chunk.try_into().unwrap());
            winterfell_arr[i] = BaseElement::new(val);
        }
        
        // Extract left digest as BaseElement array
        let left_bytes = left_digest.as_bytes();
        let mut left_arr = [BaseElement::ZERO; 4];
        for i in 0..4 {
            let chunk = &left_bytes[i * 8..(i + 1) * 8];
            let val = u64::from_le_bytes(chunk.try_into().unwrap());
            left_arr[i] = BaseElement::new(val);
        }
        
        // Extract right digest as BaseElement array
        let right_bytes = right_digest.as_bytes();
        let mut right_arr = [BaseElement::ZERO; 4];
        for i in 0..4 {
            let chunk = &right_bytes[i * 8..(i + 1) * 8];
            let val = u64::from_le_bytes(chunk.try_into().unwrap());
            right_arr[i] = BaseElement::new(val);
        }
        
        // Compute with our implementation
        let mut builder = VerifierTraceBuilder::new(256);
        // Start with left as the initial digest (in indices 0-3)
        builder.hash_state[0] = left_arr[0];
        builder.hash_state[1] = left_arr[1];
        builder.hash_state[2] = left_arr[2];
        builder.hash_state[3] = left_arr[3];
        
        // Apply merkle_step with right as sibling, direction=false (left is current).
        // direction=false corresponds to idx LSB = 0.
        builder.set_merkle_index(0);
        builder.merkle_step_from_index(right_arr);
        
        let our_digest = [
            builder.hash_state[0],
            builder.hash_state[1],
            builder.hash_state[2],
            builder.hash_state[3],
        ];
        
        assert_eq!(
            our_digest, winterfell_arr,
            "Merge mismatch: our {:?} vs winterfell {:?}",
            our_digest, winterfell_arr
        );
    }
}
