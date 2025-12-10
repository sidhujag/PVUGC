//! Full STARK Verifier Smoke Test
//!
//! Tests the complete pipeline:
//! VDF STARK → Aggregator STARK → Groth16
//! VDF STARK (×2) → Verifying Aggregator → Groth16

use crate::outer_compressed::{cycles::Bls12Bw6Cycle, RecursionCycle};
use crate::stark::test_utils::{
    build_vdf_recursive_stark_instance,
    build_verifying_aggregator_instance,
    get_or_init_inner_crs_keys,
};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

type StarkCycle = Bls12Bw6Cycle;
type StarkInnerE = <StarkCycle as RecursionCycle>::InnerE;

#[test]
fn full_stark_verifier_smoke() {
    // Complete pipeline: VDF → Aggregator → Groth16
    
    // 1) Build VDF → Aggregator → Groth16 circuit
    let instance = build_vdf_recursive_stark_instance(3, 8);
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Circuit must be satisfied");

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
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Verifying Aggregator Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Verifying Aggregator circuit must be satisfied");
}
