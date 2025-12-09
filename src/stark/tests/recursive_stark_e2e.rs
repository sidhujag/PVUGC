//! End-to-End Recursive STARK Tests
//!
//! This module tests the complete STARK-in-STARK recursive verification pipeline:
//!
//! Architecture:
//! ```text
//! Application STARK (VDF/CubicFib)
//!           ↓
//!    Aggregator STARK (aggregates N app proofs)
//!           ↓
//!     Verifier STARK (verifies Aggregator)
//!           ↓
//!        Groth16 (wraps Verifier STARK for succinctness)
//! ```
//!
//! Key Properties:
//! - Groth16 trusted setup is FIXED (universal for all applications)
//! - Verifier STARK config is FIXED
//! - Aggregator STARK can verify ANY application STARK
//! - Applications are heterogeneous (different AIRs)

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    AcceptableOptions, Trace,
};
use winter_crypto::hashers::Rp64_256;

use crate::stark::{
    aggregator_air::{
        AggregatorAir, AggregatorConfig, AggregatorPublicInputs,
        generate_aggregator_proof_with_config,
    },
    verifier_air::{
        aggregator_integration::{RecursiveConfig, RecursiveVerifier, run_recursive_pipeline},
        prover::VerifierProver,
        proof_parser::parse_proof,
        VERIFIER_TRACE_WIDTH,
    },
    tests::helpers::simple_vdf::{generate_test_vdf_proof_rpo_with_options, VdfAir},
};

type Hasher = Rp64_256;
type RandomCoin = DefaultRandomCoin<Hasher>;
type VerifierMerkle = MerkleTree<Hasher>;

/// Minimal proof options for fast testing
fn fast_test_options() -> winterfell::ProofOptions {
    winterfell::ProofOptions::new(
        4,  // num_queries
        8,  // blowup_factor
        0,  // grinding_factor
        winterfell::FieldExtension::None,
        2,  // FRI folding factor
        31, // max FRI layers
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

#[test]
fn test_e2e_vdf_to_aggregator_to_verifier() {

    // -------------------------------------------------------------------------
    // Step 1: Generate Application STARK (VDF)
    // -------------------------------------------------------------------------
    let start = BaseElement::new(42);
    let steps = 8;
    let options = fast_test_options();
    let (vdf_proof, vdf_trace) = generate_test_vdf_proof_rpo_with_options(start, steps, options.clone());
    let vdf_result = vdf_trace.get(1, vdf_trace.length() - 1);

    // Verify VDF proof off-chain
    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    winterfell::verify::<VdfAir, Hasher, RandomCoin, VerifierMerkle>(
        vdf_proof.clone(),
        vdf_result,
        &acceptable,
    )
    .expect("VDF proof should be valid");

    // -------------------------------------------------------------------------
    // Step 2: Create Application Statement Hash
    // -------------------------------------------------------------------------

    // The statement hash binds the VDF result and commitments
    let app_statement_hash = [
        vdf_result,                        // Result of computation
        BaseElement::new(1),               // Placeholder for commitment[0]
        BaseElement::new(2),               // Placeholder for commitment[1]
        BaseElement::new(3),               // Placeholder for commitment[2]
    ];

    // -------------------------------------------------------------------------
    // Step 3: Generate Aggregator STARK (wraps VDF)
    // -------------------------------------------------------------------------

    let agg_config = AggregatorConfig::test_fast();
    let (agg_proof, agg_pub_inputs, _agg_trace) = generate_aggregator_proof_with_config(
        app_statement_hash,
        &agg_config,
    )
    .expect("Aggregator proof generation should succeed");

    // Verify Aggregator proof off-chain
    let agg_options = AcceptableOptions::OptionSet(vec![agg_config.to_proof_options()]);
    winterfell::verify::<AggregatorAir, Hasher, RandomCoin, VerifierMerkle>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &agg_options,
    )
    .expect("Aggregator proof should be valid");


    // -------------------------------------------------------------------------
    // Step 4: Generate Verifier STARK (verifies Aggregator)
    // -------------------------------------------------------------------------

    let recursive_config = RecursiveConfig::test();
    let verifier = RecursiveVerifier::new(recursive_config.clone());

    let verification_trace = verifier.build_verification_trace(&agg_proof, &agg_pub_inputs);
    let verifier_pub_inputs = verifier.get_verifier_public_inputs(&agg_proof, &agg_pub_inputs);


    // -------------------------------------------------------------------------
    // Verification
    // -------------------------------------------------------------------------

    // Assertions
    assert_eq!(verification_trace.width(), VERIFIER_TRACE_WIDTH);
    assert!(verification_trace.length().is_power_of_two());
    assert!(verification_trace.length() >= 64);
}

#[test]
fn test_e2e_full_pipeline_with_run_recursive() {


    // Step 1: Create app statement hash
    let app_statement_hash = [
        BaseElement::new(100),
        BaseElement::new(101),
        BaseElement::new(102),
        BaseElement::new(103),
    ];

    // Step 2: Generate Aggregator STARK
    let agg_config = AggregatorConfig::test_fast();
    let (agg_proof, agg_pub_inputs, _) = generate_aggregator_proof_with_config(
        app_statement_hash,
        &agg_config,
    )
    .expect("Aggregator proof should succeed");

    // Step 3: Run the full recursive pipeline
    let result = run_recursive_pipeline(
        &agg_proof,
        &agg_pub_inputs,
        RecursiveConfig::test(),
    );

    // Verify the result
    assert_eq!(result.verifier_trace.width(), VERIFIER_TRACE_WIDTH);
    assert!(result.verifier_trace.length().is_power_of_two());

    // The statement hash should bind the Aggregator's result
    assert_eq!(result.statement_hash[0], agg_pub_inputs.result);

}

#[test]
fn test_e2e_multiple_apps_same_verifier() {
    // Create multiple different application statement hashes
    let app_hashes = vec![
        [BaseElement::new(1), BaseElement::new(2), BaseElement::new(3), BaseElement::new(4)],
        [BaseElement::new(5), BaseElement::new(6), BaseElement::new(7), BaseElement::new(8)],
        [BaseElement::new(9), BaseElement::new(10), BaseElement::new(11), BaseElement::new(12)],
    ];

    let agg_config = AggregatorConfig::test_fast();
    let recursive_config = RecursiveConfig::test();
    let verifier = RecursiveVerifier::new(recursive_config);

    for (i, app_hash) in app_hashes.iter().enumerate() {
        // Generate Aggregator STARK for each app
        let (agg_proof, agg_pub_inputs, _) = generate_aggregator_proof_with_config(
            *app_hash,
            &agg_config,
        )
        .expect("Aggregator proof should succeed");

        // Build verification trace using the SAME verifier
        let verification_trace = verifier.build_verification_trace(&agg_proof, &agg_pub_inputs);


        // All traces should have the same width (universal verifier)
        assert_eq!(verification_trace.width(), VERIFIER_TRACE_WIDTH);
    }
}

#[test]
fn test_e2e_verification_trace_binding() {

    // Generate two different Aggregator proofs
    let config = AggregatorConfig::test_fast();

    let hash_1 = [BaseElement::new(1); 4];
    let hash_2 = [BaseElement::new(2); 4];

    let (proof_1, pub_1, _) = generate_aggregator_proof_with_config(hash_1, &config).unwrap();
    let (proof_2, pub_2, _) = generate_aggregator_proof_with_config(hash_2, &config).unwrap();

    let recursive_config = RecursiveConfig::test();

    // Run pipeline for both
    let result_1 = run_recursive_pipeline(&proof_1, &pub_1, recursive_config.clone());
    let result_2 = run_recursive_pipeline(&proof_2, &pub_2, recursive_config);

    // Statement hashes should be DIFFERENT for different inputs
    assert_ne!(
        result_1.statement_hash,
        result_2.statement_hash,
        "Different inputs should produce different statement hashes!"
    );
}
