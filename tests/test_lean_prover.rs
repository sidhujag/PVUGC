//! Test for Lean Prover implementation
//!
//! Verifies that the "Lean Prover" (using sparse H-bases) produces valid Groth16 proofs
//! that are accepted by the standard Verifier.

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
use ark_std::{rand::SeedableRng, Zero};
use arkworks_groth16::outer_compressed::{
    OuterCircuit, InnerScalar, DefaultCycle, InnerE, OuterScalar,
};
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
use arkworks_groth16::prover_lean::{prove_lean, prove_lean_with_randomizers, LeanProvingKey};
use arkworks_groth16::ppe::{compute_baked_target, PvugcVk};
use arkworks_groth16::RecursionCycle;

#[test]
fn test_lean_prover_end_to_end() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    // 1. Get Inner Proof (Fixture)
    let fixture = get_fixture();
    // Use a circuit with NO public inputs to avoid the "Baked Quotient" divisibility issue
    // (Standard circuits mix public/witness, creating a remainder that breaks naive baking)
    let x_val = InnerScalar::<DefaultCycle>::from(10u64); 

    let circuit_inner = AddCircuit::with_public_input(x_val);
    let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng)
        .expect("inner proof failed");
    let x_inner = vec![x_val];

    // 2. Define Outer Circuit
    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner.clone(),
        proof_inner
    );

    // 3. Setup Outer PK
    let (pk_outer, vk_outer) = Groth16::< <DefaultCycle as RecursionCycle>::OuterE >::circuit_specific_setup(
        circuit_outer.clone(),
        &mut rng
    ).expect("outer setup failed");

    // 4. Convert to Lean PK
    // This step might panic if the circuit is not Baked-Quotient compatible.
    // We catch the unwind to prevent test failure if we just want to verify the API.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle>(&pk_outer, &fixture.vk_inner)
    }));

    if let Ok((_pvugc_vk, lean_pk)) = result {
        // 5. Prove using Lean Prover
        let (proof_lean, _assignment) = prove_lean(
            &lean_pk,
            circuit_outer.clone(),
            &mut rng
        ).expect("lean proving failed");

        // 6. Verify
        let public_inputs_outer =
            arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner[0]);
        let inputs_outer = vec![public_inputs_outer];


        let r_baked = compute_baked_target(
            &vk_outer,
            &_pvugc_vk,
            &inputs_outer
        ).expect("failed to compute baked target");
        
        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b);
        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        let rhs = r_baked + pairing_c_delta;
        assert_eq!(lhs, rhs, "Lean Proof + Baked Target failed verification");
    } else {
        assert!(false, "Baked Quotient setup panicked as expected for non-linear circuit.");
    }
}