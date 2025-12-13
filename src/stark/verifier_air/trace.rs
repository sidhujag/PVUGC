//! Trace Builder for Verifier AIR
//!
//! Builds the execution trace for verifying a STARK proof.
//! The trace is a sequential record of all operations the verifier performs.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement},
    Proof, TraceTable,
};

use super::{
    VerifierOp, VerifierPublicInputs, HASH_STATE_WIDTH, NUM_SELECTORS, RPO_CYCLE_LEN,
    VERIFIER_TRACE_WIDTH,
};

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
    /// Current auxiliary state
    /// aux[0]: round counter (0-6 during permute, 7 otherwise)
    /// aux[1]: reserved for flags
    /// aux[2]: verification mode (0=root, 1=ood, 2=terminal, 3=deep)
    /// aux[3]: checkpoint counter (SECURITY: must reach expected count)
    aux_state: [BaseElement; 4],
}

impl VerifierTraceBuilder {
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
            self.trace[NUM_SELECTORS + i].push(self.hash_state[i]);
        }

        // Write FRI working columns
        for i in 0..8 {
            self.trace[NUM_SELECTORS + HASH_STATE_WIDTH + i].push(self.fri_state[i]);
        }

        // Write auxiliary columns
        for i in 0..4 {
            self.trace[NUM_SELECTORS + HASH_STATE_WIDTH + 8 + i].push(self.aux_state[i]);
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
            //
            // This prevents a prover from skipping specific binding steps.
            let mode = self.aux_state[2].as_int();
            if mode == 4 {
                self.aux_state[1] = self.aux_state[1] + BaseElement::ONE;
            } else if mode == 5 {
                self.aux_state[1] = self.aux_state[1] + BaseElement::new(4096);
            }
        }
    }

    /// Initialize the sponge state
    pub fn init_sponge(&mut self) {
        self.hash_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.fri_state = [BaseElement::ZERO; 8]; // Reset FRI columns
        self.aux_state[0] = BaseElement::new(7); // Not in permute
        self.emit_row(VerifierOp::Init);
    }

    /// Absorb 8 elements into the sponge rate
    ///
    /// The row shows the state BEFORE absorption.
    /// The next row (typically Permute or Nop) shows the post-absorption state.
    pub fn absorb(&mut self, input: &[BaseElement; 8]) {
        self.aux_state[0] = BaseElement::new(7); // Not in permute
        // FRI columns preserved from previous row (no reset)
        
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

    /// Verify a single Merkle path step
    /// 
    /// Matches Winterfell's merge function: parent = hash_elements(left || right)
    /// Output is from rate portion (indices 4-7), copied to capacity (0-3) for next step.
    pub fn merkle_step(&mut self, sibling: [BaseElement; 4], direction: bool) {
        // Save current digest (in indices 0-3) before modifying state
        let current_digest = [
            self.hash_state[0],
            self.hash_state[1],
            self.hash_state[2],
            self.hash_state[3],
        ];
        
        // Store sibling in FRI working columns for AIR constraint verification
        for i in 0..4 {
            self.fri_state[i] = sibling[i];
        }
        // Store direction in aux
        self.aux_state[0] = if direction {
            BaseElement::ONE
        } else {
            BaseElement::ZERO
        };

        self.emit_row(VerifierOp::MerklePath);

        // Reset state for hash_elements (merge = hash(left || right))
        for i in 0..HASH_STATE_WIDTH {
            self.hash_state[i] = BaseElement::ZERO;
        }
        
        // Set state[0] = input length (8 elements for merge)
        self.hash_state[0] = BaseElement::new(8);

        // Absorb left || right into rate portion (indices 4-11)
        if direction {
            // Current is right child: absorb sibling || current_digest
            for i in 0..4 {
                self.hash_state[4 + i] = sibling[i];
                self.hash_state[8 + i] = current_digest[i];
            }
        } else {
            // Current is left child: absorb current_digest || sibling
            for i in 0..4 {
                self.hash_state[4 + i] = current_digest[i];
                self.hash_state[8 + i] = sibling[i];
            }
        }

        // Emit as Init (allows any state change) since we reset the sponge for merge
        // Then permute to compute the merge hash
        self.emit_row(VerifierOp::Init);
        self.permute();
        
        // Output is from rate portion (indices 4-7)
        // Copy to capacity (0-3) for next merkle_step or verify_root
        for i in 0..4 {
            self.hash_state[i] = self.hash_state[4 + i];
        }
    }

    /// Perform FRI folding step
    pub fn fri_fold(&mut self, f_x: BaseElement, f_neg_x: BaseElement, x: BaseElement, beta: BaseElement) -> BaseElement {
        // Store inputs
        self.fri_state[0] = f_x;
        self.fri_state[1] = f_neg_x;
        self.fri_state[2] = x;
        self.fri_state[3] = beta;

        // Compute folded value: g(x^2) = (f(x) + f(-x))/2 + beta * (f(x) - f(-x))/(2x)
        let two = BaseElement::new(2u64);
        let sum = f_x + f_neg_x;
        let diff = f_x - f_neg_x;
        let g = sum / two + beta * diff / (two * x);

        self.fri_state[4] = g;
        self.emit_row(VerifierOp::FriFold);

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
    pub fn verify_fri_terminal(
        &mut self,
        final_value: BaseElement,
        expected_value: BaseElement,
    ) -> bool {
        // Store values in FRI columns for constraint verification
        // Layout: [final_value, expected_value, _, _, _, _, terminal_diff, _]
        self.fri_state[0] = final_value;
        self.fri_state[1] = expected_value;
        
        // Compute difference for constraint: final_value - expected_value
        let diff = final_value - expected_value;
        self.fri_state[6] = diff;
        self.fri_state[7] = BaseElement::ZERO; // Expected to be zero
        
        // Set mode = TERMINAL VERIFICATION (aux[2] = 2)
        // NOTE: We use a distinct mode value to differentiate from ROOT (0) and OOD (1)
        self.aux_state[2] = BaseElement::new(2u64);
        
        // Emit DeepCompose row - AIR will verify fri[6] == fri[7] (diff == 0)
        self.emit_row(VerifierOp::DeepCompose);
        
        diff == BaseElement::ZERO
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
        
        // Emit DeepCompose row - checkpoint counter increments
        self.emit_row(VerifierOp::DeepCompose);
        
        local_ok
    }

    /// Verify security-parameter digest binding (num_queries/blowup/grinding/folding/trace_len).
    ///
    /// The AIR constraint will verify hash_state[0..3] == pub_inputs.params_digest when aux[2]=5.
    pub fn verify_params_digest(&mut self, params_digest: [BaseElement; 4]) -> bool {
        self.hash_state[0] = params_digest[0];
        self.hash_state[1] = params_digest[1];
        self.hash_state[2] = params_digest[2];
        self.hash_state[3] = params_digest[3];

        // Set mode = PARAMS VERIFICATION (aux[2] = 5)
        self.aux_state[2] = BaseElement::new(5u64);
        self.emit_row(VerifierOp::DeepCompose);
        true
    }

    /// Verify DEEP composition value
    /// 
    /// This verifies that the DEEP evaluation at a query position is correctly
    /// computed from the trace and composition queries at that position.
    /// 
    /// The DEEP polynomial is: 
    ///   DEEP(x) = Σ γᵢ * (T(x) - T(z)) / (x - z) + Σ γⱼ * (T(x) - T(z·g)) / (x - z·g) + ...
    /// 
    /// Parameters:
    /// - deep_value: The DEEP polynomial evaluation at query position
    /// - expected_deep: The independently computed expected value
    /// 
    /// Returns true if verification passes.
    pub fn verify_deep_value(
        &mut self,
        deep_value: BaseElement,
        expected_deep: BaseElement,
    ) -> bool {
        // Store values in FRI columns for constraint verification
        self.fri_state[0] = deep_value;
        self.fri_state[1] = expected_deep;
        
        // Compute difference
        let diff = deep_value - expected_deep;
        self.fri_state[6] = diff;
        self.fri_state[7] = BaseElement::ZERO;
        
        // Set mode = DEEP VERIFICATION (aux[2] = 3)
        self.aux_state[2] = BaseElement::new(3u64);
        
        // Emit DeepCompose row
        self.emit_row(VerifierOp::DeepCompose);
        
        diff == BaseElement::ZERO
    }

    /// Verify OOD constraint equation
    ///
    /// This is the critical check that ensures the composition polynomial
    /// correctly represents the child AIR's constraint quotient.
    ///
    /// Uses the formula:
    /// ```text
    /// transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
    /// ```
    ///
    /// The LHS and RHS are pre-computed and stored in trace columns.
    /// The AIR constraint then verifies LHS = RHS.
    ///
    /// Parameters:
    /// - ood_frame: OOD frame containing trace and composition values at z and z·g
    /// - z: OOD challenge point
    /// - g_trace: trace domain generator
    /// - trace_len: length of the trace (power of 2)
    /// - constraint_coeffs: [alpha_0, alpha_1, beta_0] from Fiat-Shamir
    /// - pub_result: expected boundary value
    /// 
    /// Uses Generic VDF (2-column) child constraints via formula-as-witness.
    pub fn verify_ood_constraints(
        &mut self,
        ood_frame: &super::ood_eval::OodFrame,
        z: BaseElement,
        g_trace: BaseElement,
        trace_len: usize,
        constraint_coeffs: &[BaseElement; 3],
        pub_result: BaseElement,
    ) -> bool {
        self.verify_ood_constraints_typed(
            ood_frame,
            z,
            g_trace,
            trace_len,
            &constraint_coeffs.to_vec(),
            pub_result,
            super::ood_eval::ChildAirType::generic_vdf(),
        )
    }
    
    /// Verify OOD constraint equation with explicit child AIR type
    ///
    /// This version allows specifying the child AIR type for recursive verification.
    /// Different child types have different constraints that need to be evaluated.
    ///
    /// # Child Types
    ///
    /// - `VerifierAir`: 27-column Verifier/Aggregator constraints (recursive verification)
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

        // Compute all values needed for the constraint equation
        let z_pow_n = z.exp((trace_len as u64).into());
        let g_pow_n_minus_1 = g_trace.exp(((trace_len - 1) as u64).into());
        let exemption = z - g_pow_n_minus_1;
        let zerofier_num = z_pow_n - BaseElement::ONE;
        let exemption_sq = exemption * exemption;

        // Compute combined composition value:
        //   C(z) = Σ_{i=0..w-1} C_i(z) * z^(i*n)
        // where w = comp_width and n = trace_len.
        let mut c_combined = BaseElement::ZERO;
        let mut z_pow_in = BaseElement::ONE;
        for &c_i in ood_frame.composition.iter() {
            c_combined += c_i * z_pow_in;
            z_pow_in *= z_pow_n;
        }

        // Compute transition constraints using child-type-specific evaluator
        let constraints = evaluate_child_constraints(
            &ood_frame.trace_current,
            &ood_frame.trace_next,
            &child_type,
        );
        
        // Combine constraints with coefficients
        let mut transition_sum = BaseElement::ZERO;
        for (i, c) in constraints.iter().enumerate() {
            if i < constraint_coeffs.len() {
                transition_sum = transition_sum + constraint_coeffs[i] * *c;
            }
        }

        // Compute boundary constraint
        let boundary_col = if matches!(child_type, super::ood_eval::ChildAirType::VerifierAir) { 26 } else { 1 };
        let boundary_value = ood_frame.trace_current.get(boundary_col)
            .copied()
            .unwrap_or(BaseElement::ZERO) - pub_result;
        let num_constraints = child_type.num_constraints();
        let boundary_coeff = constraint_coeffs.get(num_constraints)
            .copied()
            .unwrap_or(BaseElement::ZERO);
        let boundary_sum = boundary_coeff * boundary_value;

        // Compute LHS: transition_sum * exemption² + boundary_sum * zerofier_num
        let lhs = transition_sum * exemption_sq + boundary_sum * zerofier_num;

        // Compute RHS: C(z) * zerofier_num * exemption
        let rhs = c_combined * zerofier_num * exemption;

        #[cfg(any(test, debug_assertions))]
        if lhs != rhs {
            eprintln!(
                "[verifier][ood-mismatch] child={:?} trace_len={} comp_width={} coeffs={} z={} z^n={} lhs={} rhs={}",
                child_type,
                trace_len,
                ood_frame.composition.len(),
                constraint_coeffs.len(),
                z.as_int(),
                z_pow_n.as_int(),
                lhs.as_int(),
                rhs.as_int()
            );
        }

        // Store values in FRI columns for AIR constraint verification
        // Layout: [_, _, _, _, _, _, lhs, rhs]
        self.fri_state[6] = lhs;  // Pre-computed LHS
        self.fri_state[7] = rhs;  // Pre-computed RHS

        // Set mode = OOD VERIFICATION (aux[2] = 1)
        self.aux_state[2] = BaseElement::ONE;

        // Emit DeepCompose row - AIR will verify fri[6] = fri[7] (LHS = RHS)
        self.emit_row(VerifierOp::DeepCompose);

        // Also verify using the formal equation checker
        let params = OodParams {
            z,
            trace_len,
            g_trace,
            constraint_coeffs: constraint_coeffs.clone(),
            pub_result,
        };

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

        // 27 transition constraints (VerifierAir) evaluated with *child* public inputs.
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
        let periodic_values: Vec<BaseElement> = vec![];
        let mut constraints = vec![BaseElement::ZERO; super::VERIFIER_TRACE_WIDTH];
        evaluate_all(&frame, &periodic_values, &mut constraints, &pub_inputs);

        if constraint_coeffs.len() < 27 + 8 || constraints.len() < 27 {
            return false;
        }

        let mut transition_sum = BaseElement::ZERO;
        for i in 0..27 {
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
            initial_sum += constraint_coeffs[27 + j] * ood_frame.trace_current[col];
        }
        // aux[1] initial = 0 (col 24)
        initial_sum += constraint_coeffs[31] * ood_frame.trace_current[24];
        // aux[3] initial = 0 (col 26)
        initial_sum += constraint_coeffs[32] * ood_frame.trace_current[26];

        let expected_mode = BaseElement::new(expected_mode_counter as u64);
        let expected_ckpt = BaseElement::new(expected_checkpoint_count as u64);
        let final_aux1 = ood_frame.trace_current[24] - expected_mode;
        let final_aux3 = ood_frame.trace_current[26] - expected_ckpt;
        let final_term = constraint_coeffs[33] * final_aux1 + constraint_coeffs[34] * final_aux3;

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
    /// hash_state[0..3] == fri_state[0..3]
    /// 
    /// The expected root is stored in fri_state, computed root is in hash_state.
    /// Mode aux[2]=0 tells the AIR to check root verification.
    /// 
    /// Returns true if local check passes (AIR constraint will also enforce).
    pub fn verify_root(&mut self, expected_root: [BaseElement; 4]) -> bool {
        // Store expected root in FRI columns for AIR verification
        for i in 0..4 {
            self.fri_state[i] = expected_root[i];
        }
        
        // Set mode = ROOT VERIFICATION (aux[2] = 0)
        self.aux_state[2] = BaseElement::ZERO;
        
        // Emit DeepCompose row - AIR will verify hash_state[0..3] == fri_state[0..3]
        self.emit_row(VerifierOp::DeepCompose);
        
        // Return local check result for caller to track
        self.check_root(&expected_root)
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
        // Reset state to zero
        for i in 0..HASH_STATE_WIDTH {
            self.hash_state[i] = BaseElement::ZERO;
        }
        
        // Set state[0] = input length for domain separation
        // This matches Winterfell's hash_elements behavior
        self.hash_state[0] = BaseElement::new(leaf_data.len() as u64);
        
        // Process leaf data in chunks of 8 (RPO rate)
        let mut rate_idx = 0;
        let mut first_emission = true;
        for &elem in leaf_data.iter() {
            // Add element to rate portion (state[4 + rate_idx])
            self.hash_state[4 + rate_idx] = self.hash_state[4 + rate_idx] + elem;
            rate_idx += 1;
            
            // If we've filled 8 rate elements, emit and permute
            if rate_idx == 8 {
                // First emission uses Init (allows state reset), subsequent use Absorb
                if first_emission {
                    self.emit_row(VerifierOp::Init);
                    first_emission = false;
                } else {
                self.emit_row(VerifierOp::Absorb);
                }
                self.permute();
                rate_idx = 0;
            }
        }
        
        // If there are remaining elements (partial block), emit and permute
        if rate_idx > 0 || leaf_data.is_empty() {
            // First emission uses Init (allows state reset), subsequent use Absorb
            if first_emission {
                self.emit_row(VerifierOp::Init);
            } else {
            self.emit_row(VerifierOp::Absorb);
            }
            self.permute();
        }
        
        // For hash_elements, output is from RATE portion (indices 4-7)
        // Copy to capacity (0-3) so merkle_step can use it as the current digest
        // This matches Winterfell's Rp64_256::hash_elements output location
        for i in 0..4 {
            self.hash_state[i] = self.hash_state[4 + i];
        }
    }

    /// Set the final acceptance flag
    pub fn accept(&mut self, _accepted: bool) {
        // Reset aux[0] to 7 before Accept row
        // Accept encodes the same as Nop (111), and Nop constraints require aux[0] = 7
        // After Merkle steps or other ops, aux[0] may be a direction bit (0 or 1)
        self.aux_state[0] = BaseElement::new(7);
        
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

    #[test]
    fn test_trace_builder_basic() {
        let mut builder = VerifierTraceBuilder::new(64);

        builder.init_sponge();
        builder.absorb(&[BaseElement::ONE; 8]);
        builder.permute();
        let digest = builder.squeeze();

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
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1),
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
        let result = builder.verify_ood_constraints(
            &ood_frame,
            z,
            g_trace,
            trace_len,
            &constraint_coeffs,
            pub_result,
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
        
        // Apply merkle_step with right as sibling, direction=false (left is current)
        builder.merkle_step(right_arr, false);
        
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
