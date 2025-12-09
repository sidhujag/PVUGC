//! Aggregator Integration for Recursive STARK
//!
//! This module integrates the Verifier AIR with the Aggregator STARK,
//! enabling true STARK-in-STARK recursion:
//!
//! Flow:
//! 1. Application STARK (e.g., VDF) generates a proof
//! 2. Aggregator STARK aggregates multiple application proofs
//! 3. Verifier STARK verifies the Aggregator STARK
//! 4. Groth16 wraps the Verifier STARK for succinctness
//!
//! This creates a universal PVUGC system where:
//! - The Groth16 trusted setup is FIXED (verifies a single Verifier STARK config)
//! - The Verifier STARK config is FIXED (verifies any Aggregator STARK)
//! - The Aggregator STARK can verify ANY application STARK

use winterfell::{
    math::fields::f64::BaseElement,
    Proof,
};

use super::{
    merkle::MerkleDigest,
    prover::{ParsedProof, VerifierProver},
    proof_parser::parse_proof,
    VerifierPublicInputs,
};

use crate::stark::aggregator_air::{
    AggregatorAir, AggregatorConfig, AggregatorPublicInputs,
};

// ============================================================================
// RECURSIVE VERIFICATION CONTEXT
// ============================================================================

/// Configuration for the recursive verification pipeline
#[derive(Clone, Debug)]
pub struct RecursiveConfig {
    /// Configuration for the Aggregator STARK
    pub aggregator_config: AggregatorConfig,

    /// Configuration for the Verifier STARK
    pub verifier_options: winterfell::ProofOptions,
}

impl RecursiveConfig {
    /// Create a test configuration with minimal parameters
    pub fn test() -> Self {
        Self {
            aggregator_config: AggregatorConfig::test_fast(),
            verifier_options: winterfell::ProofOptions::new(
                4,  // num_queries
                64, // blowup_factor (must be >= max constraint degree + 1, we have degree 50)
                0,  // grinding_factor
                winterfell::FieldExtension::None,
                2,  // FRI folding factor
                31, // max FRI layers
                winterfell::BatchingMethod::Linear,
                winterfell::BatchingMethod::Linear,
            ),
        }
    }

    /// Create a production configuration with full security
    pub fn production_128bit() -> Self {
        Self {
            aggregator_config: AggregatorConfig::production_128bit(),
            verifier_options: winterfell::ProofOptions::new(
                28, // num_queries
                16, // blowup_factor
                12, // grinding_factor
                winterfell::FieldExtension::None,
                4,  // FRI folding factor
                31, // max FRI layers
                winterfell::BatchingMethod::Linear,
                winterfell::BatchingMethod::Linear,
            ),
        }
    }
}

// ============================================================================
// RECURSIVE VERIFIER
// ============================================================================

/// Recursive STARK Verifier
///
/// Takes an Aggregator STARK proof and produces a Verifier STARK proof
/// that can then be verified by Groth16.
pub struct RecursiveVerifier {
    config: RecursiveConfig,
    verifier_prover: VerifierProver,
}

impl RecursiveVerifier {
    /// Create a new recursive verifier
    pub fn new(config: RecursiveConfig) -> Self {
        let verifier_prover = VerifierProver::new(config.verifier_options.clone());
        Self {
            config,
            verifier_prover,
        }
    }

    /// Parse an Aggregator STARK proof and build verification trace
    pub fn build_verification_trace(
        &self,
        aggregator_proof: &Proof,
        aggregator_pub_inputs: &AggregatorPublicInputs,
    ) -> winterfell::TraceTable<BaseElement> {
        // Parse the aggregator proof
        let parsed = parse_aggregator_proof(aggregator_proof, aggregator_pub_inputs);

        // Build the verification trace
        self.verifier_prover.build_verification_trace(&parsed)
    }

    /// Get the public inputs for the Verifier STARK
    pub fn get_verifier_public_inputs(
        &self,
        aggregator_proof: &Proof,
        aggregator_pub_inputs: &AggregatorPublicInputs,
    ) -> VerifierPublicInputs {
        let parsed = parse_aggregator_proof(aggregator_proof, aggregator_pub_inputs);

        // Compute trace domain generator for the given trace length
        // g_trace = ω^(2^64 / trace_len) where ω is primitive root of Goldilocks
        let g_trace = compute_trace_generator(parsed.trace_len);

        VerifierPublicInputs {
            statement_hash: hash_aggregator_statement(aggregator_pub_inputs),
            trace_commitment: parsed.trace_commitment,
            comp_commitment: parsed.comp_commitment,
            fri_commitments: parsed.fri_commitments,
            num_queries: parsed.num_queries,
            proof_trace_len: parsed.trace_len,
            g_trace,
            pub_result: aggregator_pub_inputs.result,
        }
    }

    /// Get the Verifier STARK prover
    pub fn prover(&self) -> &VerifierProver {
        &self.verifier_prover
    }

    /// Get the configuration
    pub fn config(&self) -> &RecursiveConfig {
        &self.config
    }
}

// ============================================================================
// PROOF PARSING
// ============================================================================

/// Parse an Aggregator STARK proof into our format
fn parse_aggregator_proof(
    proof: &Proof,
    pub_inputs: &AggregatorPublicInputs,
) -> ParsedProof {
    parse_proof::<AggregatorAir>(proof, pub_inputs)
}

/// Hash the Aggregator's public inputs into a statement hash
fn hash_aggregator_statement(pub_inputs: &AggregatorPublicInputs) -> MerkleDigest {
    // The statement hash binds all the public inputs together
    // This is what gets verified by Groth16
    //
    // We include:
    // - result: The final accumulated VDF result
    // - children_root[0..2]: First two elements of the children Merkle root
    //
    // This provides cryptographic binding between the STARK proof and
    // the statement that Groth16 ultimately verifies.
    [
        pub_inputs.result,
        pub_inputs.children_root[0],
        pub_inputs.children_root[1],
        pub_inputs.children_root[2],
    ]
}

/// Compute trace domain generator for a given trace length
///
/// For Goldilocks field, we need g such that g^trace_len = 1.
/// This uses the 2-adic root of unity for power-of-2 trace lengths.
fn compute_trace_generator(trace_len: usize) -> BaseElement {
    use winterfell::math::FieldElement;
    
    // Goldilocks 2^32-th root of unity (from Winterfell)
    const TWO_ADIC_ROOT: u64 = 1753635133440165772;
    
    let log_trace_len = (trace_len as u64).trailing_zeros();
    
    // g = TWO_ADIC_ROOT^(2^(32 - log_trace_len))
    let exp = 1u64 << (32 - log_trace_len);
    BaseElement::new(TWO_ADIC_ROOT).exp(exp.into())
}

// ============================================================================
// FULL PIPELINE
// ============================================================================

/// Result of the recursive verification pipeline
#[derive(Clone)]
pub struct RecursiveResult {
    /// The Verifier STARK trace
    pub verifier_trace: winterfell::TraceTable<BaseElement>,

    /// The public inputs for Groth16
    pub verifier_pub_inputs: VerifierPublicInputs,

    /// Statement hash that Groth16 verifies
    pub statement_hash: MerkleDigest,
}

/// Run the full recursive verification pipeline
///
/// Takes an Aggregator proof and returns data needed for Groth16 wrapping
pub fn run_recursive_pipeline(
    aggregator_proof: &Proof,
    aggregator_pub_inputs: &AggregatorPublicInputs,
    config: RecursiveConfig,
) -> RecursiveResult {
    let verifier = RecursiveVerifier::new(config);

    let verifier_trace = verifier.build_verification_trace(
        aggregator_proof,
        aggregator_pub_inputs,
    );

    let verifier_pub_inputs = verifier.get_verifier_public_inputs(
        aggregator_proof,
        aggregator_pub_inputs,
    );

    let statement_hash = hash_aggregator_statement(aggregator_pub_inputs);

    RecursiveResult {
        verifier_trace,
        verifier_pub_inputs,
        statement_hash,
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::aggregator_air::generate_aggregator_proof_with_config;
    use crate::stark::verifier_air::VERIFIER_TRACE_WIDTH;
    use winterfell::Trace;

    #[test]
    fn test_recursive_config() {
        let config = RecursiveConfig::test();
        // test_fast uses 2 queries
        assert_eq!(config.aggregator_config.num_queries, 2);
        assert_eq!(config.verifier_options.num_queries(), 4);
    }

    #[test]
    fn test_recursive_verifier_creation() {
        let config = RecursiveConfig::test();
        let verifier = RecursiveVerifier::new(config);

        // test_fast uses 2 queries
        assert_eq!(verifier.config().aggregator_config.num_queries, 2);
    }

    #[test]
    fn test_aggregator_to_verifier_trace() {
        println!("\n=== Aggregator → Verifier Trace Test ===\n");

        // Step 1: Create a simulated application statement hash
        let app_statement_hash = [
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
            BaseElement::new(4),
        ];
        println!("✓ Created application statement hash");

        // Step 2: Generate aggregator proof
        let config = AggregatorConfig::test_fast();
        let result = generate_aggregator_proof_with_config(app_statement_hash, &config);
        let (proof, pub_inputs, _trace) = result.expect("Aggregator proof generation failed");
        println!("✓ Generated aggregator proof (trace_len={})", proof.context.trace_info().length());

        // Step 3: Build verification trace
        let recursive_config = RecursiveConfig::test();
        let verifier = RecursiveVerifier::new(recursive_config);
        let verification_trace = verifier.build_verification_trace(&proof, &pub_inputs);

        println!("✓ Built verification trace");
        println!("  - Width: {}", verification_trace.width());
        println!("  - Length: {}", verification_trace.length());

        assert_eq!(verification_trace.width(), VERIFIER_TRACE_WIDTH);
        assert!(verification_trace.length().is_power_of_two());
    }

    #[test]
    fn test_full_recursive_pipeline() {
        println!("\n=== Full Recursive Pipeline Test ===\n");

        // Step 1: Create application statement hash
        let app_statement_hash = [
            BaseElement::new(7),
            BaseElement::new(8),
            BaseElement::new(9),
            BaseElement::new(10),
        ];

        // Step 2: Generate aggregator proof
        let agg_config = AggregatorConfig::test_fast();
        let result = generate_aggregator_proof_with_config(app_statement_hash, &agg_config);
        let (proof, pub_inputs, _trace) = result.expect("Aggregator proof generation failed");

        println!("Aggregator proof generated:");
        println!("  - Trace length: {}", proof.context.trace_info().length());
        println!("  - Num queries: {}", proof.options().num_queries());

        // Step 3: Run recursive pipeline
        let result = run_recursive_pipeline(
            &proof,
            &pub_inputs,
            RecursiveConfig::test(),
        );

        println!("\nRecursive pipeline result:");
        println!("  - Verifier trace length: {}", result.verifier_trace.length());
        println!("  - Statement hash: {:?}", result.statement_hash);

        // Verify the statement hash binds the aggregator's result
        assert_eq!(result.statement_hash[0], pub_inputs.result);
        assert_eq!(result.statement_hash[1], pub_inputs.children_root[0]);
    }

    #[test]
    fn test_statement_hash_binding() {
        let pub_inputs = AggregatorPublicInputs {
            result: BaseElement::new(1),
            children_root: [BaseElement::new(3), BaseElement::new(4), BaseElement::new(5), BaseElement::new(6)],
            initial_state: [BaseElement::new(7), BaseElement::new(8), BaseElement::new(9), BaseElement::new(10)],
            final_state: [BaseElement::new(11), BaseElement::new(12), BaseElement::new(13), BaseElement::new(14)],
        };

        let hash = hash_aggregator_statement(&pub_inputs);

        // Statement hash should bind result and children_root
        assert_eq!(hash[0], pub_inputs.result);
        assert_eq!(hash[1], pub_inputs.children_root[0]);
        assert_eq!(hash[2], pub_inputs.children_root[1]);
        assert_eq!(hash[3], pub_inputs.children_root[2]);
    }
}
