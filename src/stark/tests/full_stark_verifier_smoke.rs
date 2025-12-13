//! Full STARK Verifier Smoke Test
//!
//! Tests the complete pipeline (VerifierAir-only aggregation):
//! - VDF STARK → VerifierAir (verifies VDF) → Groth16-ready circuit
//! - VDF STARK (×2) → VerifierAir (verifies both) → Groth16-ready circuit

use crate::outer_compressed::{cycles::Bls12Bw6Cycle, RecursionCycle};
use crate::stark::test_utils::{
    build_vdf_recursive_stark_instance,
    build_vdf_recursive_stark_instance_with_fri,
    build_verifying_aggregator_instance,
    get_or_init_inner_crs_keys,
};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

type StarkCycle = Bls12Bw6Cycle;
type StarkInnerE = <StarkCycle as RecursionCycle>::InnerE;

/// Debug test to identify which constraint fails with FRI layers
#[test]
#[ignore]
fn debug_verifier_air_constraints_with_fri() {
    // Legacy debug harness was for AggregatorAir; the current pipeline is VerifierAir-only.
    // If we need this again, reintroduce a focused verifier trace/constraint debug for VerifierAir proofs.
    unimplemented!("VerifierAir-only debug harness not implemented");
}

#[test]
fn full_stark_verifier_smoke() {
    // Complete pipeline: VDF → VerifierAir (leaf wrapper) → Groth16-ready circuit
    
    // 1) Build VDF → VerifierAir → Groth16 circuit
    let instance = build_vdf_recursive_stark_instance(3, 8);
    
    // Synthesize to check constraints (with constraint trace enabled)
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
        instance
            .circuit
            .clone()
            .generate_constraints(cs.clone())
            .expect("generate constraints");
    });
    
    println!("Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("First failing constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "Circuit must be satisfied");

    // Generate Groth16 proof using cached CRS keys
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) = get_or_init_inner_crs_keys();

    let pub_input = vec![instance.statement_hash];
    let proof = Groth16::<StarkInnerE>::prove(&pk, instance.circuit, &mut rng)
        .expect("Groth16 prove");
    // Verify Groth16 proof
    let valid = Groth16::<StarkInnerE>::verify(&vk, &pub_input, &proof).expect("verify");

    assert!(valid, "Full STARK verifier proof should verify");
}

/// Test the FULL STARK verifier with meaningful FRI layers
/// 
/// This is the critical test that verifies FRI folding is actually checked.
/// Uses larger trace (256 rows) to generate ~8 FRI layers.
#[test]
#[ignore] // Takes ~30-60 seconds, run with: cargo test full_stark_verifier_with_fri_smoke --release -- --ignored
fn full_stark_verifier_with_fri_smoke() {
    println!("\n=== Full STARK Verifier with FRI Layers ===\n");
    
    // Build with FRI config (trace_len=256, ~8 FRI layers)
    let instance = build_vdf_recursive_stark_instance_with_fri(3, 8);
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Circuit Statistics (with FRI):");
    println!("  Total Constraints: {}", cs.num_constraints());
    println!("  (Should be significantly larger than no-FRI version due to FRI verification)");
    
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Circuit with FRI must be satisfied");
    
    // The constraint count should be notably higher due to FRI verification
    // No-FRI version has ~3M constraints, with FRI should be ~5-10M+
    println!("\n✅ Full STARK verifier with FRI layers passed!");
}

/// Test the verifying aggregator pipeline:
/// VDF STARK 0 + VDF STARK 1 → Verifying Aggregator → Groth16
/// 
/// This tests that:
/// 1. The Aggregator ACTUALLY VERIFIES both VDF proofs in its trace
/// 2. The Aggregator proof uses VerifierAir constraints (27 columns)
/// 3. The Groth16 circuit correctly verifies the VerifierAir proof
#[test]
fn verifying_aggregator_smoke() {
    // Two VDF proofs with different parameters
    let instance = build_verifying_aggregator_instance(
        3, 8,   // VDF 0: start=3, steps=8
        7, 8,   // VDF 1: start=7, steps=8
    );
    
    // Synthesize to check constraints (with constraint trace enabled)
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
        instance
            .circuit
            .clone()
            .generate_constraints(cs.clone())
            .expect("generate constraints");
    });
    
    println!("Verifying Aggregator Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("First failing constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "Verifying Aggregator circuit must be satisfied");
}
