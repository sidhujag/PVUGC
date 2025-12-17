//! End-to-End Recursive STARK Tests (two-AIR pipeline)
//!
//! ```text
//! App proof
//!   ↓
//! AggregatorAir proof (leaf wrapper / app binding lives here)
//!   ↓
//! VerifierAir proof (verifies AggregatorAir)
//!   ↓
//! Groth16/R1CS verifies VerifierAir
//! ```

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    AcceptableOptions, Prover, Trace,
};
use winter_crypto::hashers::Rp64_256;
use winter_crypto::ElementHasher;

use crate::stark::{
    aggregator_air::{AggregatorAir, AggregatorConfig, prove_aggregator_leaf_from_app},
    verifier_air::{
        proof_parser::parse_proof,
        ood_eval::ChildAirType,
        VerifierAir,
    },
    test_utils::prove_verifier_air_over_child,
    tests::helpers::simple_vdf::{build_vdf_trace, VdfAir, VdfProver},
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
        31, // production-style terminal remainder (degree ≤ 31)
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    )
}

fn digest_to_merkle_digest<D: winter_crypto::Digest>(digest: &D) -> [BaseElement; 4] {
    let bytes = digest.as_bytes();
    [
        BaseElement::new(u64::from_le_bytes(bytes[0..8].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[8..16].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[16..24].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[24..32].try_into().unwrap())),
    ]
}

#[test]
fn test_e2e_add2_app_to_aggregator_air_to_verifier_air() {

    // -------------------------------------------------------------------------
    // Step 1: Generate Application STARK (simple VDF)
    // -------------------------------------------------------------------------
    let steps = 8;
    let options = fast_test_options();
    let start = BaseElement::ZERO;
    let app_trace = build_vdf_trace(start, steps);
    let app_result = app_trace.get(1, app_trace.length() - 1);
    let app_proof = VdfProver::<Hasher>::new(options.clone())
        .prove(app_trace.clone())
        .expect("VDF proof generation failed");

    // Verify VDF proof off-chain
    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    winterfell::verify::<VdfAir, Hasher, RandomCoin, VerifierMerkle>(
        app_proof.clone(),
        app_result,
        &acceptable,
    )
    .expect("VDF proof should be valid");

    // -------------------------------------------------------------------------
    // Step 2: AggregatorAir leaf wrapper over the app statement hash
    // -------------------------------------------------------------------------
    let agg_cfg = AggregatorConfig::test_fast();
    let (agg_proof, agg_pub_inputs, _agg_trace) =
        prove_aggregator_leaf_from_app::<VdfAir>(&agg_cfg, app_proof.clone(), app_result, ChildAirType::generic_vdf())
            .expect("AggregatorAir leaf proof failed");

    // Sanity: AggregatorAir verifies natively.
    let acceptable_agg = AcceptableOptions::OptionSet(vec![agg_cfg.to_proof_options()]);
    winterfell::verify::<AggregatorAir, Hasher, RandomCoin, VerifierMerkle>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    )
    .expect("AggregatorAir proof should verify");

    // -------------------------------------------------------------------------
    // Step 3: VerifierAir proof verifying the AggregatorAir proof
    // -------------------------------------------------------------------------
    let parsed_agg = parse_proof::<AggregatorAir>(&agg_proof, &agg_pub_inputs);
    let verifier_options = winterfell::ProofOptions::new(
        2, 64, 0,
        winterfell::FieldExtension::None,
        2, 1,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let (verifier_proof, verifier_pub_inputs) =
        prove_verifier_air_over_child(&parsed_agg, ChildAirType::aggregator_air(), verifier_options.clone());

    let acceptable_verifier = AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Hasher, RandomCoin, VerifierMerkle>(
        verifier_proof,
        verifier_pub_inputs,
        &acceptable_verifier,
    )
    .expect("VerifierAir over AggregatorAir should verify");
}

#[test]
fn test_e2e_aggregator_air_leaf_statements_differ_for_different_add2_instances() {
    let steps = 8;
    let options = fast_test_options();

    let t0 = build_vdf_trace(BaseElement::new(0), steps);
    let p0 = VdfProver::<Hasher>::new(options.clone()).prove(t0.clone()).unwrap();
    let out0 = t0.get(1, t0.length() - 1);
    let t1 = build_vdf_trace(BaseElement::new(5), steps);
    let p1 = VdfProver::<Hasher>::new(options.clone()).prove(t1.clone()).unwrap();
    let out1 = t1.get(1, t1.length() - 1);

    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    winterfell::verify::<VdfAir, Hasher, RandomCoin, VerifierMerkle>(p0.clone(), out0, &acceptable).unwrap();
    winterfell::verify::<VdfAir, Hasher, RandomCoin, VerifierMerkle>(p1.clone(), out1, &acceptable).unwrap();

    let h0 = digest_to_merkle_digest(&Hasher::hash_elements(&[out0]));
    let h1 = digest_to_merkle_digest(&Hasher::hash_elements(&[out1]));
    assert_ne!(h0, h1);
}
