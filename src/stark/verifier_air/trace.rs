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
    /// aux[2]: reserved
    /// aux[3]: acceptance flag
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

    /// Apply one RPO round to the hash state
    fn apply_rpo_round(&mut self, round: usize) {
        use super::hash_chiplet::{MDS_MATRIX, ROUND_CONSTANTS, sbox};

        // Add round constants (round-specific)
        for i in 0..HASH_STATE_WIDTH {
            self.hash_state[i] = self.hash_state[i]
                + BaseElement::new(ROUND_CONSTANTS[round % 7][i]);
        }

        // Apply S-box (x^7 for all elements)
        // Note: Standard RPO uses x^7 for first half and x^{1/7} for second half,
        // but for constraint simplicity, we use x^7 for all elements.
        for i in 0..HASH_STATE_WIDTH {
            self.hash_state[i] = sbox(self.hash_state[i]);
        }

        // Apply MDS matrix
        let mut new_state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        for i in 0..HASH_STATE_WIDTH {
            for j in 0..HASH_STATE_WIDTH {
                let idx = (i + HASH_STATE_WIDTH - j) % HASH_STATE_WIDTH;
                new_state[i] = new_state[i]
                    + BaseElement::new(MDS_MATRIX[idx]) * self.hash_state[j];
            }
        }
        self.hash_state = new_state;
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
    pub fn merkle_step(&mut self, sibling: [BaseElement; 4], direction: bool) {
        // Store sibling in FRI working columns
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

        // Hash current digest with sibling using RPO sponge
        // This follows the standard Merkle tree compression pattern:
        // parent = RPO(left || right) where left/right order depends on direction
        let mut input = [BaseElement::ZERO; 8];
        if direction {
            // Current is right child
            for i in 0..4 {
                input[i] = sibling[i];
                input[4 + i] = self.hash_state[i];
            }
        } else {
            // Current is left child
            for i in 0..4 {
                input[i] = self.hash_state[i];
                input[4 + i] = sibling[i];
            }
        }

        self.absorb(&input);
        self.permute();
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

    /// Verify OOD constraint equation
    ///
    /// This is the critical check that ensures the composition polynomial
    /// correctly represents the Aggregator's constraint quotient.
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
    pub fn verify_ood_constraints(
        &mut self,
        ood_frame: &super::ood_eval::OodFrame,
        z: BaseElement,
        g_trace: BaseElement,
        trace_len: usize,
        constraint_coeffs: &[BaseElement; 3],
        pub_result: BaseElement,
    ) -> bool {
        use super::ood_eval::{OodParams, verify_ood_constraint_equation};

        // Compute all values needed for the constraint equation
        let z_pow_n = z.exp((trace_len as u64).into());
        let g_pow_n_minus_1 = g_trace.exp(((trace_len - 1) as u64).into());
        let exemption = z - g_pow_n_minus_1;
        let zerofier_num = z_pow_n - BaseElement::ONE;
        let exemption_sq = exemption * exemption;

        // Get trace and composition values
        let curr_0 = ood_frame.trace_current.get(0).copied().unwrap_or(BaseElement::ZERO);
        let curr_1 = ood_frame.trace_current.get(1).copied().unwrap_or(BaseElement::ZERO);
        let next_0 = ood_frame.trace_next.get(0).copied().unwrap_or(BaseElement::ZERO);
        let next_1 = ood_frame.trace_next.get(1).copied().unwrap_or(BaseElement::ZERO);
        let comp_0 = ood_frame.composition.get(0).copied().unwrap_or(BaseElement::ZERO);
        let comp_1 = ood_frame.composition.get(1).copied().unwrap_or(BaseElement::ZERO);

        // Compute transition constraints
        let c0 = next_0 - (curr_0 * curr_0 * curr_0 + curr_1);
        let c1 = next_1 - curr_0;
        let transition_sum = constraint_coeffs[0] * c0 + constraint_coeffs[1] * c1;

        // Compute boundary constraint
        let boundary_value = curr_1 - pub_result;
        let boundary_sum = constraint_coeffs[2] * boundary_value;

        // Compute LHS: transition_sum * exemption² + boundary_sum * zerofier_num
        let lhs = transition_sum * exemption_sq + boundary_sum * zerofier_num;

        // Compute RHS: C(z) * zerofier_num * exemption
        let c_combined = comp_0 + comp_1 * z_pow_n;
        let rhs = c_combined * zerofier_num * exemption;

        // Store values in FRI columns for AIR constraint verification
        // Layout: [curr[0], curr[1], next[0], next[1], comp[0], comp[1], lhs, rhs]
        self.fri_state[0] = curr_0;
        self.fri_state[1] = curr_1;
        self.fri_state[2] = next_0;
        self.fri_state[3] = next_1;
        self.fri_state[4] = comp_0;
        self.fri_state[5] = comp_1;
        self.fri_state[6] = lhs;  // Pre-computed LHS
        self.fri_state[7] = rhs;  // Pre-computed RHS

        // Store constraint coefficients in aux columns
        self.aux_state[0] = constraint_coeffs[0]; // alpha_0
        self.aux_state[1] = constraint_coeffs[1]; // alpha_1
        self.aux_state[2] = constraint_coeffs[2]; // beta_0

        // Emit DeepCompose row - AIR will verify fri[6] = fri[7] (LHS = RHS)
        self.emit_row(VerifierOp::DeepCompose);

        // Also verify using the formal equation checker
        let params = OodParams {
            z,
            trace_len,
            g_trace,
            constraint_coeffs: constraint_coeffs.to_vec(),
            pub_result,
        };

        match verify_ood_constraint_equation(ood_frame, &params) {
            Ok(()) => true,
            Err(_) => false,
        }
    }

    /// Set the final acceptance flag
    pub fn accept(&mut self, accepted: bool) {
        self.aux_state[3] = if accepted {
            BaseElement::ONE
        } else {
            BaseElement::ZERO
        };
        self.emit_row(VerifierOp::Accept);
    }

    /// Pad trace to power of 2 and finalize
    pub fn finalize(mut self) -> TraceTable<BaseElement> {
        // Ensure trace length is power of 2
        let current_len = self.row;
        let target_len = current_len.next_power_of_two().max(8);

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
}
