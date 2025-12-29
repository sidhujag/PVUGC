
//! Test for Lean Prover implementation
//!
//! Verifies that the "Lean Prover" (using sparse H-bases) produces valid Groth16 proofs
//! that are accepted by the standard Verifier.

use ark_ec::pairing::Pairing;
use ark_groth16::{r1cs_to_qap::PvugcReduction, Groth16};
use ark_snark::SNARK;
use ark_std::{rand::SeedableRng, UniformRand, Zero};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterScalar,
};
use arkworks_groth16::ppe::compute_baked_target;
use arkworks_groth16::prover_lean::{prove_lean, prove_lean_with_randomizers};
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
use arkworks_groth16::test_circuits::TwoInputCircuit;
use arkworks_groth16::test_fixtures::get_fixture_two_input;
use arkworks_groth16::RecursionCycle;
use arkworks_groth16::decap::build_commitments;

#[test]
#[ignore]
fn test_lean_prover_end_to_end() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    // 1. Get Inner Proof (Fixture)
    //
    // Use a two-public-input inner circuit to match SP1-style statements:
    // - instance_variables includes the implicit 1, so this yields "+3 inputs" in logs.
    let fixture = get_fixture_two_input();

    // Runtime statement - this would be a hash in production (e.g., Bitcoin UTXO)
    let input1 = InnerScalar::<DefaultCycle>::from(1001001000122u64);
    let input2 = InnerScalar::<DefaultCycle>::from(999_000_111_222u64);
    let x_inner = vec![input1, input2];

    // PRODUCTION SIMULATION: Runtime proof can use any seed!
    // With algebraic q_const computation, setup doesn't depend on proof coords.
    const RUNTIME_SEED: u64 = 12345;

    let circuit_inner = TwoInputCircuit::new(input1, input2);
    let mut runtime_rng = ark_std::rand::rngs::StdRng::seed_from_u64(RUNTIME_SEED);
    let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut runtime_rng)
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
        let input1 = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let input2 = statements
            .get(1)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = TwoInputCircuit::new(input1, input2);
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
        // 5. First verify STANDARD Groth16 works (sanity check)
        let _circuit_std = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner.clone(),
            proof_inner.clone(),
        );
        let inputs_outer: Vec<OuterScalar<DefaultCycle>> = x_inner
            .iter()
            .map(arkworks_groth16::outer_compressed::fr_inner_to_outer)
            .collect();

        // 6. Prove using Lean Prover
        let circuit_lean = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner.clone(),
            proof_inner.clone(),
        );
        let (proof_lean, _assignment) =
            prove_lean(&lean_pk, circuit_lean, &mut rng).expect("lean proving failed");

        // 8. Verify lean proof
        let r_baked = compute_baked_target(&vk_outer, &_pvugc_vk, &inputs_outer)
            .expect("failed to compute baked target");

        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b);
        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        let rhs = r_baked + pairing_c_delta;
        assert_eq!(lhs, rhs, "Lean Proof + Baked Target failed verification");
    } else {
        assert!(
            false,
            "Baked Quotient setup panicked as expected for non-linear circuit."
        );
    }
}

/// Test proof-agnostic extraction property:
/// - Two proofs of SAME statement → SAME key
/// - Two proofs of DIFFERENT statements → DIFFERENT keys
#[test]
#[ignore]
fn test_outer_circuit_proof_agnostic() {
    use arkworks_groth16::pvugc_outer::{
        arm_columns_outer_for, build_column_bases_outer_for, compute_r_to_rho_outer_for,
        compute_target_outer_for,
    };

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    // Match the Lean Prover E2E test shape: inner statement has *two* public inputs.
    let fixture = get_fixture_two_input();

    // Use separate RNG for inner proofs so outer setup RNG stays consistent.
    // In production, inner proofs are runtime-generated and can use any seed.
    let mut inner_rng_1 = ark_std::rand::rngs::StdRng::seed_from_u64(1234);
    let mut inner_rng_2 = ark_std::rand::rngs::StdRng::seed_from_u64(5678);

    // === STATEMENT 1 ===
    let x1a = InnerScalar::<DefaultCycle>::from(10u64);
    let x1b = InnerScalar::<DefaultCycle>::from(11u64);
    let x_inner_1 = vec![x1a, x1b];

    // Generate TWO different inner proofs for the SAME statement (different inner randomness).
    let circuit_inner_1a = TwoInputCircuit::new(x1a, x1b);
    let proof_inner_1a =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner_1a, &mut inner_rng_1)
            .expect("inner proof 1a failed");
    let circuit_inner_1b = TwoInputCircuit::new(x1a, x1b);
    let proof_inner_1b =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner_1b, &mut inner_rng_2)
            .expect("inner proof 1b failed");

    // === STATEMENT 2 (DIFFERENT) ===
    let y1 = InnerScalar::<DefaultCycle>::from(20u64);
    let y2 = InnerScalar::<DefaultCycle>::from(21u64);
    let x_inner_2 = vec![y1, y2];

    let circuit_inner_2 = TwoInputCircuit::new(y1, y2);
    let proof_inner_2 =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner_2, &mut inner_rng_1)
            .expect("inner proof 2 failed");

    // Setup outer circuit
    let circuit_outer_1 = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner_1.clone(),
        proof_inner_1a.clone(),
    );

    let (pk_outer, vk_outer) =
        Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::circuit_specific_setup(
            circuit_outer_1.clone(),
            &mut rng,
        )
        .expect("outer setup failed");

    // Build lean PK with PVUGC VK
    let pk_inner_clone = fixture.pk_inner.clone();
    let inner_proof_generator = move |statements: &[InnerScalar<DefaultCycle>]| {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(99999);
        let input1 = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let input2 = statements
            .get(1)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = TwoInputCircuit::new(input1, input2);
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

    if let Ok((pvugc_vk, lean_pk)) = result {
        // === ARMING ===
        let rho = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let public_inputs_1: Vec<OuterScalar<DefaultCycle>> = x_inner_1
            .iter()
            .map(arkworks_groth16::outer_compressed::fr_inner_to_outer)
            .collect();
        let public_inputs_2: Vec<OuterScalar<DefaultCycle>> = x_inner_2
            .iter()
            .map(arkworks_groth16::outer_compressed::fr_inner_to_outer)
            .collect();

        // Arm for statement 1
        let bases_1 = build_column_bases_outer_for::<DefaultCycle>(&pvugc_vk, &vk_outer, &public_inputs_1);
        let arms_1 = arm_columns_outer_for::<DefaultCycle>(&bases_1, &rho);

        // Arm for statement 2
        let bases_2 = build_column_bases_outer_for::<DefaultCycle>(&pvugc_vk, &vk_outer, &public_inputs_2);
        let arms_2 = arm_columns_outer_for::<DefaultCycle>(&bases_2, &rho);

        // === PROOF 1A: First proof of statement 1 ===
        let circuit_1a = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner_1.clone(),
            proof_inner_1a.clone(),
        );
        let r1 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let s1 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let (proof_1a, assignment_1a) = prove_lean_with_randomizers(&lean_pk, circuit_1a, r1, s1)
            .expect("proof 1a failed");
        let num_instance = vk_outer.gamma_abc_g1.len();
        let commits_1a = build_commitments::<<DefaultCycle as RecursionCycle>::OuterE>(
            &proof_1a.a, &proof_1a.c, &s1, &assignment_1a, num_instance
        );

        // === PROOF 1B: Second proof of statement 1 (DIFFERENT randomness) ===
        let circuit_1b = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner_1.clone(),
            proof_inner_1b.clone(),
        );
        let r2 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let s2 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let (proof_1b, assignment_1b) = prove_lean_with_randomizers(&lean_pk, circuit_1b, r2, s2)
            .expect("proof 1b failed");
        let commits_1b = build_commitments::<<DefaultCycle as RecursionCycle>::OuterE>(
            &proof_1b.a, &proof_1b.c, &s2, &assignment_1b, num_instance
        );

        // === PROOF 2: Proof of statement 2 ===
        let circuit_2 = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner_2.clone(),
            proof_inner_2.clone(),
        );
        let r3 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let s3 = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let (proof_2, assignment_2) = prove_lean_with_randomizers(&lean_pk, circuit_2, r3, s3)
            .expect("proof 2 failed");
        let commits_2 = build_commitments::<<DefaultCycle as RecursionCycle>::OuterE>(
            &proof_2.a, &proof_2.c, &s3, &assignment_2, num_instance
        );

        // === DECAP ===
        let k_1a = arkworks_groth16::decap::decap(&commits_1a, &arms_1).expect("decap 1a failed");
        let k_1b = arkworks_groth16::decap::decap(&commits_1b, &arms_1).expect("decap 1b failed");
        let k_2 = arkworks_groth16::decap::decap(&commits_2, &arms_2).expect("decap 2 failed");

        // === EXPECTED KEYS ===
        let r_1 = compute_target_outer_for::<DefaultCycle>(&vk_outer, &pvugc_vk, &x_inner_1);
        let k_expected_1 = compute_r_to_rho_outer_for::<DefaultCycle>(&r_1, &rho);

        let r_2 = compute_target_outer_for::<DefaultCycle>(&vk_outer, &pvugc_vk, &x_inner_2);
        let k_expected_2 = compute_r_to_rho_outer_for::<DefaultCycle>(&r_2, &rho);

        // === ASSERTIONS ===
        
        // 1. Both proofs of statement 1 extract the SAME key
        assert_eq!(
            k_1a, k_1b,
            "PROOF-AGNOSTIC FAILED: Two proofs of SAME statement should yield SAME key!"
        );

        // 2. Keys match expected R^ρ
        assert_eq!(
            k_1a, k_expected_1,
            "Key 1a doesn't match expected R₁^ρ"
        );
        assert_eq!(
            k_2, k_expected_2,
            "Key 2 doesn't match expected R₂^ρ"
        );

        // 3. Different statements extract DIFFERENT keys
        assert_ne!(
            k_1a, k_2,
            "STATEMENT-DEPENDENT FAILED: Different statements should yield DIFFERENT keys!"
        );

        println!("✅ PROOF-AGNOSTIC: Two proofs of same statement → same key");
        println!("✅ STATEMENT-DEPENDENT: Different statements → different keys");
        println!("✅ Outer circuit proof-agnostic extraction VERIFIED!");
    } else {
        panic!("PVUGC setup failed unexpectedly");
    }
}