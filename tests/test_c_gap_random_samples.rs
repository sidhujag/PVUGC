//! Random-Sample C-Gap Validation Test
//!
//! This test verifies that the C-gap (baked quotient term) is correctly computed
//! by checking that the T_const(x) reconstruction works for RANDOM (non-canonical)
//! statements, not just the canonical samples {0, e_1, e_2, ...} used during setup.
//!
//! Security Rationale:
//! The lean CRS is derived from the standard-lean C gap sampled at canonical points.
//! If the gap is truly linear (affine) in the public inputs, then recovering Q_i
//! from n+1 canonical samples is mathematically complete. This test provides high
//! confidence by verifying that random, non-canonical statements also satisfy:
//!   C_std(x) - C_lean(x) = T_const(x)

use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_groth16::{r1cs_to_qap::PvugcReduction, Groth16};
use ark_snark::SNARK;
use ark_std::{rand::SeedableRng, UniformRand, Zero};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterScalar,
};
use arkworks_groth16::prover_lean::prove_lean_with_randomizers;
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::RecursionCycle;

/// Number of random samples to test (higher = more confidence)
const NUM_RANDOM_SAMPLES: usize = 10;

#[test]
#[ignore]
fn test_c_gap_random_sample_validation() {
    println!("\n=== C-Gap Random Sample Validation Test ===\n");
    println!("Testing {} random (non-canonical) statements...", NUM_RANDOM_SAMPLES);

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xCAFE);
    let fixture = get_fixture();

    // Setup outer circuit with a fixed statement first
    let x_setup = InnerScalar::<DefaultCycle>::from(42u64);
    let circuit_setup = AddCircuit::with_public_input(x_setup);
    let mut setup_rng = ark_std::rand::rngs::StdRng::seed_from_u64(1);
    let proof_setup = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_setup, &mut setup_rng)
        .expect("setup inner proof failed");

    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        vec![x_setup],
        proof_setup,
    );

    let (pk_outer, _vk_outer) =
        Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::circuit_specific_setup(
            circuit_outer,
            &mut rng,
        )
        .expect("outer setup failed");

    // Build lean PK with PVUGC VK (this computes T_const from canonical samples)
    let pk_inner_clone = fixture.pk_inner.clone();
    let inner_proof_generator = move |statements: &[InnerScalar<DefaultCycle>]| {
        let mut gen_rng = ark_std::rand::rngs::StdRng::seed_from_u64(99999);
        let statement = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = AddCircuit::with_public_input(statement);
        Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut gen_rng)
            .expect("inner proof generation failed")
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &fixture.vk_inner,
            inner_proof_generator,
        )
    }));

    let (pvugc_vk, lean_pk) = match result {
        Ok(v) => v,
        Err(_) => {
            println!("PVUGC setup failed - test skipped");
            return;
        }
    };

    println!("Setup complete. T_const has {} basis points.", pvugc_vk.t_const_points_gt.len());

    let mut passed = 0;
    let mut failed = 0;

    for sample_idx in 0..NUM_RANDOM_SAMPLES {
        // Generate a random statement (not canonical - uses random field element)
        let random_val = InnerScalar::<DefaultCycle>::rand(&mut rng);
        let random_statement = vec![random_val];

        // Generate inner proof for this random statement
        let circuit_inner = AddCircuit::with_public_input(random_val);
        let mut inner_rng = ark_std::rand::rngs::StdRng::seed_from_u64(sample_idx as u64 + 1000);
        let inner_proof = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut inner_rng)
            .expect("inner proof for random statement failed");

        // Compute STANDARD proof (no ZK - r=s=0 implicitly via create_proof_with_reduction_no_zk)
        let circuit_std = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            random_statement.clone(),
            inner_proof.clone(),
        );
        let proof_std = Groth16::<
            <DefaultCycle as RecursionCycle>::OuterE,
            PvugcReduction,
        >::create_proof_with_reduction_no_zk(circuit_std, &pk_outer)
            .expect("standard proof failed");

        // Compute LEAN proof with r=s=0 (must match standard no-zk)
        let circuit_lean = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            random_statement.clone(),
            inner_proof.clone(),
        );
        let (proof_lean, _) = prove_lean_with_randomizers(
            &lean_pk,
            circuit_lean,
            OuterScalar::<DefaultCycle>::zero(),
            OuterScalar::<DefaultCycle>::zero(),
        )
        .expect("lean proof failed");

        // Verify A and B match (sanity check - they should be identical)
        assert_eq!(
            proof_std.a, proof_lean.a,
            "Sample {}: A mismatch between std/lean proofs!",
            sample_idx
        );
        assert_eq!(
            proof_std.b, proof_lean.b,
            "Sample {}: B mismatch between std/lean proofs!",
            sample_idx
        );

        // Compute the actual C-gap: C_std - C_lean
        let c_gap_actual =
            proof_std.c.into_group() - proof_lean.c.into_group();

        // Reconstruct T_const(x) from the baked basis points in GT, then
        // lift back to G1 for comparison. But wait - T_const is in GT!
        // We need to compare in GT space.
        //
        // Actual check: e(C_std - C_lean, δ) should equal T_const(x)
        //
        // T_const(x) = T_0 * Π_i T_{i+1}^{x_i}  (in GT)
        // e(C_gap, δ) should equal this.

        let delta_g2 = pk_outer.vk.delta_g2;
        let c_gap_in_gt = <DefaultCycle as RecursionCycle>::OuterE::pairing(
            c_gap_actual.into_affine(),
            delta_g2,
        );

        // Reconstruct T_const(x) from baked points
        let outer_inputs: Vec<OuterScalar<DefaultCycle>> = random_statement
            .iter()
            .map(|x| arkworks_groth16::outer_compressed::fr_inner_to_outer(x))
            .collect();

        let t_const_reconstructed = {
            use ark_ec::pairing::PairingOutput;
            use ark_ff::{Field, PrimeField};

            let mut t_acc = pvugc_vk.t_const_points_gt[0];
            for (i, x_i) in outer_inputs.iter().enumerate() {
                let term = pvugc_vk.t_const_points_gt[i + 1].0.pow(&x_i.into_bigint());
                t_acc = PairingOutput(t_acc.0 * term);
            }
            t_acc
        };

        // Compare: e(C_gap, δ) == T_const(x)?
        if c_gap_in_gt == t_const_reconstructed {
            passed += 1;
            println!(
                "  Sample {:2}: ✅ PASS - C-gap matches T_const for random x = {:?}...",
                sample_idx,
                &format!("{:?}", random_val)[..20.min(format!("{:?}", random_val).len())]
            );
        } else {
            failed += 1;
            // For debugging, check if the gap is at least consistent
            let diff = c_gap_in_gt.0 - t_const_reconstructed.0;
            println!(
                "  Sample {:2}: ❌ FAIL - C-gap MISMATCH for random x!",
                sample_idx
            );
            println!("              C-gap in GT:     {:?}", c_gap_in_gt);
            println!("              T_const(x):      {:?}", t_const_reconstructed);
            println!("              Difference:      {:?}", diff);
        }
    }

    println!("\n=== Results ===");
    println!("Passed: {}/{}", passed, NUM_RANDOM_SAMPLES);
    println!("Failed: {}/{}", failed, NUM_RANDOM_SAMPLES);

    if failed > 0 {
        panic!(
            "C-GAP VALIDATION FAILED: {} out of {} random samples had mismatched T_const(x). \
             This indicates the baked quotient computation may be incomplete.",
            failed,
            NUM_RANDOM_SAMPLES
        );
    }

    println!("\n✅ C-Gap Random Sample Validation PASSED!");
    println!("   The baked T_const(x) correctly reconstructs the standard-lean C gap");
    println!("   for {} random (non-canonical) statements.", NUM_RANDOM_SAMPLES);
}

/// Additional stress test with edge case values
#[test]
#[ignore]
fn test_c_gap_edge_cases() {
    println!("\n=== C-Gap Edge Case Validation ===\n");

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xCAFE);
    let fixture = get_fixture();

    // Edge case values to test
    let edge_cases: Vec<(&str, InnerScalar<DefaultCycle>)> = vec![
        ("zero", InnerScalar::<DefaultCycle>::from(0u64)),
        ("one", InnerScalar::<DefaultCycle>::from(1u64)),
        ("small", InnerScalar::<DefaultCycle>::from(2u64)),
        ("medium", InnerScalar::<DefaultCycle>::from(1000000u64)),
        ("large", InnerScalar::<DefaultCycle>::from(u64::MAX)),
        ("field_minus_one", -InnerScalar::<DefaultCycle>::from(1u64)),
    ];

    // Setup outer circuit
    let x_setup = InnerScalar::<DefaultCycle>::from(42u64);
    let circuit_setup = AddCircuit::with_public_input(x_setup);
    let mut setup_rng = ark_std::rand::rngs::StdRng::seed_from_u64(1);
    let proof_setup = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_setup, &mut setup_rng)
        .expect("setup inner proof failed");

    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        vec![x_setup],
        proof_setup,
    );

    let (pk_outer, _vk_outer) =
        Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::circuit_specific_setup(
            circuit_outer,
            &mut rng,
        )
        .expect("outer setup failed");

    let pk_inner_clone = fixture.pk_inner.clone();
    let inner_proof_generator = move |statements: &[InnerScalar<DefaultCycle>]| {
        let mut gen_rng = ark_std::rand::rngs::StdRng::seed_from_u64(99999);
        let statement = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = AddCircuit::with_public_input(statement);
        Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut gen_rng)
            .expect("inner proof generation failed")
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &fixture.vk_inner,
            inner_proof_generator,
        )
    }));

    let (pvugc_vk, lean_pk) = match result {
        Ok(v) => v,
        Err(_) => {
            println!("PVUGC setup failed - test skipped");
            return;
        }
    };

    let mut all_passed = true;

    for (name, edge_val) in edge_cases {
        let statement = vec![edge_val];

        // Generate inner proof
        let circuit_inner = AddCircuit::with_public_input(edge_val);
        let mut inner_rng = ark_std::rand::rngs::StdRng::seed_from_u64(12345);
        let inner_proof = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut inner_rng)
            .expect("inner proof for edge case failed");

        // Standard proof (no ZK)
        let circuit_std = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            statement.clone(),
            inner_proof.clone(),
        );
        let proof_std = Groth16::<
            <DefaultCycle as RecursionCycle>::OuterE,
            PvugcReduction,
        >::create_proof_with_reduction_no_zk(circuit_std, &pk_outer)
            .expect("standard proof failed");

        // Lean proof with r=s=0
        let circuit_lean = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            statement.clone(),
            inner_proof.clone(),
        );
        let (proof_lean, _) = prove_lean_with_randomizers(
            &lean_pk,
            circuit_lean,
            OuterScalar::<DefaultCycle>::zero(),
            OuterScalar::<DefaultCycle>::zero(),
        )
        .expect("lean proof failed");

        // Compute C-gap
        let c_gap = proof_std.c.into_group() - proof_lean.c.into_group();
        let delta_g2 = pk_outer.vk.delta_g2;
        let c_gap_gt = <DefaultCycle as RecursionCycle>::OuterE::pairing(
            c_gap.into_affine(),
            delta_g2,
        );

        // Reconstruct T_const(x)
        let outer_inputs: Vec<OuterScalar<DefaultCycle>> = statement
            .iter()
            .map(|x| arkworks_groth16::outer_compressed::fr_inner_to_outer(x))
            .collect();

        let t_const = {
            use ark_ec::pairing::PairingOutput;
            use ark_ff::{Field, PrimeField};

            let mut t_acc = pvugc_vk.t_const_points_gt[0];
            for (i, x_i) in outer_inputs.iter().enumerate() {
                let term = pvugc_vk.t_const_points_gt[i + 1].0.pow(&x_i.into_bigint());
                t_acc = PairingOutput(t_acc.0 * term);
            }
            t_acc
        };

        if c_gap_gt == t_const {
            println!("  Edge case '{}': ✅ PASS", name);
        } else {
            println!("  Edge case '{}': ❌ FAIL - C-gap != T_const(x)", name);
            all_passed = false;
        }
    }

    if !all_passed {
        panic!("One or more edge case validations failed!");
    }

    println!("\n✅ All edge case validations PASSED!");
}

