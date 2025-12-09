//! Integration Tests for Verifier AIR
//!
//! Tests the complete verification flow end-to-end.

#[cfg(test)]
mod tests {
    use winterfell::math::{fields::f64::BaseElement, FieldElement};

    use crate::stark::verifier_air::{
        fri::{fold_evaluation, FriConfig},
        merkle::{MerkleDigest, MerklePath, MerkleTree, rpo_compress},
        ood_eval::{evaluate_aggregator_constraints, OodFrame},
        transcript::{derive_challenges, Transcript},
        trace::VerifierTraceBuilder,
        HASH_STATE_WIDTH,
    };

    /// Helper to create a test digest
    fn make_digest(seed: u64) -> MerkleDigest {
        [
            BaseElement::new(seed),
            BaseElement::new(seed + 1),
            BaseElement::new(seed + 2),
            BaseElement::new(seed + 3),
        ]
    }

    /// Test the complete Merkle verification flow
    #[test]
    fn test_merkle_verification_flow() {
        // Create a Merkle tree with 8 leaves
        let leaves: Vec<MerkleDigest> = (0..8)
            .map(|i| make_digest(i * 10))
            .collect();

        let tree = MerkleTree::new(leaves.clone());

        // Get paths for all leaves
        for i in 0..8 {
            let path = tree.get_path(i);
            let computed_root = path.verify(&leaves[i]);
            assert_eq!(computed_root, tree.root(), "Path {} should verify", i);
        }

        // Verify that wrong leaf fails
        let wrong_leaf = make_digest(999);
        let path = tree.get_path(0);
        let computed_root = path.verify(&wrong_leaf);
        assert_ne!(computed_root, tree.root());
    }

    /// Test the Fiat-Shamir transcript flow
    #[test]
    fn test_fiat_shamir_flow() {
        let mut transcript = Transcript::new();

        // Simulate absorbing proof context
        transcript.absorb(BaseElement::new(8));  // trace_len
        transcript.absorb(BaseElement::new(2));  // trace_width
        transcript.absorb(BaseElement::new(64)); // lde_domain_size

        // Absorb trace commitment
        let trace_commit = make_digest(100);
        for &e in &trace_commit {
            transcript.absorb(e);
        }

        // Derive OOD challenge z
        let z0 = transcript.squeeze();
        let z1 = transcript.squeeze();
        
        // z should be non-trivial
        assert_ne!(z0, BaseElement::ZERO);
        assert_ne!(z1, BaseElement::ZERO);

        // Absorb OOD frame
        for i in 0..4 {
            transcript.absorb(BaseElement::new(i + 200));
        }

        // Derive constraint coefficients
        let coeffs = transcript.squeeze_many(2);
        assert_eq!(coeffs.len(), 2);

        // Different proofs should give different challenges
        let mut transcript2 = Transcript::new();
        transcript2.absorb(BaseElement::new(16)); // Different trace_len
        let z0_alt = transcript2.squeeze();
        assert_ne!(z0, z0_alt);
    }

    /// Test OOD constraint evaluation
    #[test]
    fn test_ood_constraint_evaluation() {
        // Simulate a valid VDF step
        // col0[i+1] = col0[i]^3 + col1[i]
        // col1[i+1] = col0[i]
        let col0 = BaseElement::new(3);
        let col1 = BaseElement::new(5);

        // Compute correct next values
        let next0 = col0 * col0 * col0 + col1; // 3^3 + 5 = 32
        let next1 = col0; // 3

        // Evaluate constraints
        let constraints = evaluate_aggregator_constraints(
            &[col0, col1],
            &[next0, next1],
        );

        // Should be zero for valid transition
        assert_eq!(constraints[0], BaseElement::ZERO);
        assert_eq!(constraints[1], BaseElement::ZERO);

        // Invalid transition should give non-zero constraints
        let bad_next0 = BaseElement::new(30); // Wrong!
        let bad_constraints = evaluate_aggregator_constraints(
            &[col0, col1],
            &[bad_next0, next1],
        );
        assert_ne!(bad_constraints[0], BaseElement::ZERO);
    }

    /// Test FRI folding arithmetic
    #[test]
    fn test_fri_folding_arithmetic() {
        // Test case: constant polynomial (f(x) = f(-x) = c)
        let c = BaseElement::new(42);
        let x = BaseElement::new(7);
        let beta = BaseElement::new(3);

        // For constant: g(x²) = c regardless of beta
        let folded = fold_evaluation(c, c, x, beta);
        assert_eq!(folded, c);

        // Test case: odd polynomial (f(x) = -f(-x))
        let f_x = BaseElement::new(10);
        let f_neg_x = BaseElement::ZERO - f_x;
        let x = BaseElement::new(5);
        let beta = BaseElement::ONE;

        // sum = 0, diff = 20
        // g = 0 + 1 * 20 / 10 = 2
        let folded = fold_evaluation(f_x, f_neg_x, x, beta);
        assert_eq!(folded, BaseElement::new(2));
    }

    /// Test trace builder creates valid trace structure
    #[test]
    fn test_trace_builder_structure() {
        let mut builder = VerifierTraceBuilder::new(128);

        // Simulate verification flow
        builder.init_sponge();
        
        // Absorb some data
        let absorb_data: [BaseElement; 8] = core::array::from_fn(|i| BaseElement::new((i + 1) as u64));
        builder.absorb(&absorb_data);
        builder.permute();
        
        // Squeeze challenge
        let _challenge = builder.squeeze();
        
        // Merkle verification step
        let sibling = make_digest(100);
        builder.merkle_step(sibling, false);
        
        // FRI fold
        let _folded = builder.fri_fold(
            BaseElement::new(10),
            BaseElement::new(10),
            BaseElement::new(3),
            BaseElement::new(1),
        );
        
        // Final accept
        builder.accept(true);

        // Finalize and check structure
        let trace = builder.finalize();
        
        use winterfell::Trace;
        assert!(trace.length().is_power_of_two());
        assert_eq!(trace.width(), crate::stark::verifier_air::VERIFIER_TRACE_WIDTH);
    }

    /// Test complete challenge derivation
    #[test]
    fn test_complete_challenge_derivation() {
        let mut transcript = Transcript::new();

        let trace_commit = make_digest(1);
        let comp_commit = make_digest(2);
        let fri_commits = vec![make_digest(3), make_digest(4)];
        let ood_current = vec![BaseElement::new(10), BaseElement::new(11)];
        let ood_next = vec![BaseElement::new(12), BaseElement::new(13)];
        let ood_comp = vec![BaseElement::new(20)];

        let challenges = derive_challenges(
            &mut transcript,
            &trace_commit,
            &ood_current,
            &ood_next,
            &ood_comp,
            &comp_commit,
            &fri_commits,
            2,   // num_constraint_coeffs
            2,   // trace_width
            1,   // comp_width
            4,   // num_queries
            128, // lde_domain_size
        );

        // Check all challenges were derived
        assert_eq!(challenges.z.len(), 2);
        assert_eq!(challenges.constraint_coeffs.len(), 2);
        assert_eq!(challenges.deep_trace_coeffs.len(), 4); // 2 * trace_width
        assert_eq!(challenges.deep_comp_coeffs.len(), 1);
        assert_eq!(challenges.fri_betas.len(), 2);
        assert_eq!(challenges.query_positions.len(), 4);

        // Query positions should be sorted and in range
        for i in 1..challenges.query_positions.len() {
            assert!(challenges.query_positions[i] > challenges.query_positions[i-1]);
        }
        for &pos in &challenges.query_positions {
            assert!(pos < 128);
        }
    }

    /// Test that RPO compression is consistent with Merkle tree
    #[test]
    fn test_rpo_merkle_consistency() {
        let left = make_digest(1);
        let right = make_digest(2);

        // Manual compression
        let parent = rpo_compress(&left, &right);

        // Via Merkle tree
        let tree = MerkleTree::new(vec![left, right]);
        
        // Root should match
        assert_eq!(tree.root(), parent);
    }

    /// Test end-to-end verification simulation
    #[test]
    fn test_verification_simulation() {
        // This simulates what the verifier AIR would do

        // 1. Build Merkle tree for trace
        let trace_values: Vec<MerkleDigest> = (0..8)
            .map(|i| make_digest(i * 100))
            .collect();
        let trace_tree = MerkleTree::new(trace_values.clone());

        // 2. Derive challenges from transcript
        let mut transcript = Transcript::new();
        transcript.absorb_digest(&trace_tree.root());
        let z = transcript.squeeze_extension();
        
        // 3. Simulate OOD evaluation
        let ood_current = vec![BaseElement::new(5), BaseElement::new(7)];
        // Compute valid next step
        let next0 = ood_current[0] * ood_current[0] * ood_current[0] + ood_current[1];
        let ood_next = vec![next0, ood_current[0]];

        // 4. Verify constraints at OOD point
        let constraints = evaluate_aggregator_constraints(&ood_current, &ood_next);
        assert!(constraints.iter().all(|c| *c == BaseElement::ZERO));

        // 5. Verify Merkle paths for queried positions
        transcript.absorb_many(&ood_current);
        transcript.absorb_many(&ood_next);
        
        let query_pos = (transcript.squeeze().as_int() as usize) % 8;
        let path = trace_tree.get_path(query_pos);
        let computed = path.verify(&trace_values[query_pos]);
        assert_eq!(computed, trace_tree.root());

        // 6. Simulate FRI folding
        let fri_beta = transcript.squeeze();
        let f_x = BaseElement::new(42);
        let f_neg_x = BaseElement::new(42);
        let x = BaseElement::new(7);
        let folded = fold_evaluation(f_x, f_neg_x, x, fri_beta);
        
        // For symmetric values, should equal original
        assert_eq!(folded, f_x);
    }
}
