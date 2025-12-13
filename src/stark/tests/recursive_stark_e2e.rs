//! End-to-End Recursive STARK Tests
//!
//! This module tests the complete STARK-in-STARK recursive verification pipeline:
//!
//! Architecture:
//! ```text
//! Application STARK (e.g. Add2/VDF)
//!           ↓
//!   VerifierAir STARK (verifies child STARK proofs; can be used as an aggregation node)
//!           ↓
//!        Groth16 (wraps VerifierAir for succinctness)
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
    verifier_air::{
        VerifierAir,
        proof_parser::parse_proof,
        prover::VerifierProver,
        ood_eval::ChildAirType,
        VERIFIER_TRACE_WIDTH,
    },
    aggregator_air::generate_verifying_aggregator_proof,
    tests::helpers::add2::{generate_test_add2_proof_rpo_with_options, Add2Air},
};

type Hasher = Rp64_256;
type RandomCoin = DefaultRandomCoin<Hasher>;
type VerifierMerkle = MerkleTree<Hasher>;

/// Minimal proof options for fast testing
fn fast_test_options() -> winterfell::ProofOptions {
    winterfell::ProofOptions::new(
        2,  // num_queries
        8,  // blowup_factor
        0,  // grinding_factor
        winterfell::FieldExtension::None,
        2,  // FRI folding factor
        31, // max FRI remainder size
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

#[test]
fn test_e2e_add2_to_verifier_air_single_child() {

    // -------------------------------------------------------------------------
    // Step 1: Generate Application STARK (Add2)
    // -------------------------------------------------------------------------
    let steps = 8;
    let options = fast_test_options();
    let (app_proof, app_trace) =
        generate_test_add2_proof_rpo_with_options(BaseElement::ZERO, steps, options.clone());
    let app_result = app_trace.get(1, app_trace.length() - 1);

    // Verify Add2 proof off-chain
    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    winterfell::verify::<Add2Air, Hasher, RandomCoin, VerifierMerkle>(
        app_proof.clone(),
        app_result,
        &acceptable,
    )
    .expect("Add2 proof should be valid");

    // -------------------------------------------------------------------------
    // Step 2: Build VerifierAir trace (verifying the application proof)
    // -------------------------------------------------------------------------
    let parsed = parse_proof::<Add2Air>(&app_proof, &app_result);
    let verifier = VerifierProver::new(options.clone());
    let verification_trace = verifier.build_verification_trace(&parsed, ChildAirType::generic_add2());


    // -------------------------------------------------------------------------
    // Verification
    // -------------------------------------------------------------------------

    // Assertions
    assert_eq!(verification_trace.width(), VERIFIER_TRACE_WIDTH);
    assert!(verification_trace.length().is_power_of_two());
    assert!(verification_trace.length() >= 64);
}

#[test]
fn test_e2e_verifying_aggregator_verifies_two_add2_children() {
    // Two different Add2 instances (different trace length => different output).
    let leaf_options = fast_test_options();
    let acceptable = AcceptableOptions::OptionSet(vec![leaf_options.clone()]);

    // VerifierAir proof options must satisfy VerifierAir's minimum blowup requirements.
    let verifier_options = winterfell::ProofOptions::new(
        2,   // num_queries
        64,  // blowup_factor (VerifierAir requires large blowup)
        0,   // grinding_factor
        winterfell::FieldExtension::None,
        2,   // FRI folding factor
        31,  // max FRI layers
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let (p0, t0) = generate_test_add2_proof_rpo_with_options(BaseElement::new(0), 8, leaf_options.clone());
    let out0 = t0.get(1, t0.length() - 1);
    winterfell::verify::<Add2Air, Hasher, RandomCoin, VerifierMerkle>(p0.clone(), out0, &acceptable)
        .expect("child0 should verify");

    let (p1, t1) = generate_test_add2_proof_rpo_with_options(BaseElement::new(5), 8, leaf_options.clone());
    let out1 = t1.get(1, t1.length() - 1);
    winterfell::verify::<Add2Air, Hasher, RandomCoin, VerifierMerkle>(p1.clone(), out1, &acceptable)
        .expect("child1 should verify");

    // Parse both and build a *verifying aggregator node* (VerifierAir proof verifying both).
    let child0 = parse_proof::<Add2Air>(&p0, &out0);
    let child1 = parse_proof::<Add2Air>(&p1, &out1);
    // (sanity) parsed proof carries widths/params used by recursive verifier

    let packed = ((child0.fri_folding_factor as u64) << 32) | (child0.grinding_factor as u64);
    let expected_child_params_digest = [
        BaseElement::new(child0.trace_len as u64),
        BaseElement::new(child0.lde_blowup as u64),
        BaseElement::new(child0.num_queries as u64),
        BaseElement::new(packed),
    ];
    let (agg_proof, agg_pub_inputs, _agg_trace) = generate_verifying_aggregator_proof(
        &child0,
        ChildAirType::generic_add2(),
        &child1,
        ChildAirType::generic_add2(),
        expected_child_params_digest,
        verifier_options.clone(),
    )
    .expect("verifying-aggregator proof should succeed");

    // Verify the verifying-aggregator (VerifierAir) proof off-chain.
    let acceptable_agg = AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Hasher, RandomCoin, VerifierMerkle>(
        agg_proof,
        agg_pub_inputs,
        &acceptable_agg,
    )
    .expect("verifying-aggregator should verify");
}

#[test]
fn test_e2e_multiple_add2_instances_same_verifier_trace_width() {
    let options = fast_test_options();
    let verifier = VerifierProver::new(options.clone());
    let child_type = ChildAirType::generic_add2();

    for &steps in &[8usize, 16usize, 32usize] {
        let (p, t) = generate_test_add2_proof_rpo_with_options(BaseElement::ZERO, steps, options.clone());
        let out = t.get(1, t.length() - 1);
        let parsed = parse_proof::<Add2Air>(&p, &out);
        let trace = verifier.build_verification_trace(&parsed, child_type.clone());
        assert_eq!(trace.width(), VERIFIER_TRACE_WIDTH);
    }
}

#[test]
fn test_e2e_verifying_aggregator_statement_hash_differs_for_different_children() {
    let leaf_options = fast_test_options();
    let verifier_options = winterfell::ProofOptions::new(
        2, 64, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let (p0, t0) = generate_test_add2_proof_rpo_with_options(BaseElement::new(0), 8, leaf_options.clone());
    let out0 = t0.get(1, t0.length() - 1);
    let (p1, t1) = generate_test_add2_proof_rpo_with_options(BaseElement::new(5), 8, leaf_options.clone());
    let out1 = t1.get(1, t1.length() - 1);

    let child0 = parse_proof::<Add2Air>(&p0, &out0);
    let child1 = parse_proof::<Add2Air>(&p1, &out1);

    let packed = ((child0.fri_folding_factor as u64) << 32) | (child0.grinding_factor as u64);
    let expected_child_params_digest = [
        BaseElement::new(child0.trace_len as u64),
        BaseElement::new(child0.lde_blowup as u64),
        BaseElement::new(child0.num_queries as u64),
        BaseElement::new(packed),
    ];
    let (_proof_a, pub_a, _) = generate_verifying_aggregator_proof(
        &child0,
        ChildAirType::generic_add2(),
        &child1,
        ChildAirType::generic_add2(),
        expected_child_params_digest,
        verifier_options.clone(),
    )
    .expect("proof A should succeed");

    let (p2, t2) = generate_test_add2_proof_rpo_with_options(BaseElement::new(9), 8, leaf_options);
    let out2 = t2.get(1, t2.length() - 1);
    let child2 = parse_proof::<Add2Air>(&p2, &out2);
    let (_proof_b, pub_b, _) = generate_verifying_aggregator_proof(
        &child0,
        ChildAirType::generic_add2(),
        &child2,
        ChildAirType::generic_add2(),
        expected_child_params_digest,
        verifier_options,
    )
    .expect("proof B should succeed");

    assert_ne!(pub_a.statement_hash, pub_b.statement_hash);
}
