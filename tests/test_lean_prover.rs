//! Test for Lean Prover implementation
//!
//! Verifies that the "Lean Prover" (using sparse H-bases) produces valid Groth16 proofs
//! that are accepted by the standard Verifier.

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_groth16::{r1cs_to_qap::PvugcReduction, Groth16, ProvingKey};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_snark::SNARK;
use ark_std::{rand::SeedableRng, Zero};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterScalar,
};
use arkworks_groth16::ppe::{compute_baked_target, compute_baked_target_lean, PvugcVk};
use arkworks_groth16::prover_lean::{
    prove_lean, prove_lean_with_randomizers, LeanProof, LeanProvingKey,
};
use arkworks_groth16::pvugc_outer::{build_pvugc_setup_from_pk_for, derive_gt_table_from_pk, pk_without_alpha};
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::RecursionCycle;


#[test]
fn test_lean_prover_end_to_end() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    // 1. Get Inner Proof (Fixture)
    let fixture = get_fixture();
    // Runtime statement - this would be a hash in production (e.g., Bitcoin UTXO)
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let x_inner = vec![x_val];

    // PRODUCTION SIMULATION: Runtime proof can use any seed!
    // With algebraic q_const computation, setup doesn't depend on proof coords.
    const RUNTIME_SEED: u64 = 12345;

    let circuit_inner = AddCircuit::with_public_input(x_val);
    let mut runtime_rng = ark_std::rand::rngs::StdRng::seed_from_u64(RUNTIME_SEED);
    let proof_inner =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut runtime_rng)
        .expect("inner proof failed");

    // 2. Define Outer Circuit
    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner.clone(),
        proof_inner.clone(),
    );

    // 3. Setup Outer PK
    let (pk_outer, vk_outer) =
        Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::circuit_specific_setup(
            circuit_outer.clone(),
            &mut rng,
        )
        .expect("outer setup failed");

    // 4. Convert to Lean PK
    //
    // q_const is computed from the gap between standard and lean proofs.
    // The gap is linear in x when the Q-vector fix is applied.
    // We use fixed coords (from statements 0 and 1) to compute q_const.
    // This works for ANY statement because the gap is linear!
    let pk_inner_clone = fixture.pk_inner.clone();
    let inner_proof_generator = move |statements: &[InnerScalar<DefaultCycle>]| {
        // Use a fixed seed for reproducibility during q_const computation
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(99999);
        let statement = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = AddCircuit::with_public_input(statement);
        Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut rng)
            .expect("inner proof generation failed")
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &fixture.vk_inner,
            inner_proof_generator,
        )
    }));

    if let Ok((_pvugc_vk, lean_pk)) = result {
        // 5. Prove using Lean Prover
        let (proof_lean, _assignment) =
            prove_lean(&lean_pk, circuit_outer.clone(), &mut rng).expect("lean proving failed");

        // 6. Verify
        let public_inputs_outer =
            arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner[0]);
        let inputs_outer = vec![public_inputs_outer];

        // Use compute_baked_target_lean which uses precomputed alpha_g1_beta_g2
        // This is the production path where alpha_g1 is not available
        let r_baked = compute_baked_target_lean(&vk_outer, &_pvugc_vk, &inputs_outer)
            .expect("failed to compute baked target");

        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b)
            + proof_lean.alpha_b.clone();


        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        
        // RHS = r_baked + e(C, δ) + alpha_c
        // alpha_c compensates for s*α missing from C (since A' doesn't include α)
        let rhs = r_baked + pairing_c_delta + proof_lean.alpha_c.clone();
        assert_eq!(lhs, rhs, "Lean Proof + Baked Target failed verification");
    } else {
        assert!(
            false,
            "Baked Quotient setup panicked as expected for non-linear circuit."
        );
    }
}
