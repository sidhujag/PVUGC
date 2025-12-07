
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
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::RecursionCycle;
use arkworks_groth16::decap::build_commitments;

#[test]
#[ignore]
fn test_lean_prover_end_to_end() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    // 1. Get Inner Proof (Fixture)
    let fixture = get_fixture();

    // Runtime statement - this would be a hash in production (e.g., Bitcoin UTXO)
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let x_inner = vec![x_val];

    // PRODUCTION SIMULATION: Runtime proof can use any seed!
    // With algebraic q_const computation, setup doesn't depend on proof coords.
    const RUNTIME_SEED: u64 = 99999;

    let circuit_inner = AddCircuit::with_public_input(x_val);
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
        // 5. First verify STANDARD Groth16 works (sanity check)
        let circuit_std = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner.clone(),
            proof_inner.clone(),
        );
        let proof_std = Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::prove(
            &pk_outer,
            circuit_std,
            &mut rng,
        ).expect("standard proof failed");
        
        let public_inputs_outer =
            arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner[0]);
        let inputs_outer = vec![public_inputs_outer];
        
        let std_valid = Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::verify(
            &vk_outer,
            &inputs_outer,
            &proof_std,
        ).expect("standard verify failed");
        println!("[DEBUG] Standard Groth16 verification: {}", std_valid);
        assert!(std_valid, "Standard Groth16 proof should verify!");

        // 6. Prove using Lean Prover
        let circuit_lean = OuterCircuit::<DefaultCycle>::new(
            (*fixture.vk_inner).clone(),
            x_inner.clone(),
            proof_inner.clone(),
        );
        let (proof_lean, _assignment) =
            prove_lean(&lean_pk, circuit_lean, &mut rng).expect("lean proving failed");

        // 7. Compare standard vs lean proof elements
        println!("[DEBUG] Standard A == Lean A: {}", proof_std.a == proof_lean.a);
        println!("[DEBUG] Standard B == Lean B: {}", proof_std.b == proof_lean.b);
        println!("[DEBUG] Standard C == Lean C: {}", proof_std.c == proof_lean.c);

        // 8. Verify lean proof
        let r_baked = compute_baked_target(&vk_outer, &_pvugc_vk, &inputs_outer)
            .expect("failed to compute baked target");

        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b);
        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        let rhs = r_baked + pairing_c_delta;
        
        // Debug: Also check what standard proof gives
        let lhs_std = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_std.a, proof_std.b);
        let rhs_std_c = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_std.c, vk_outer.delta_g2);
        println!("[DEBUG] LHS (lean e(A,B)): {:?}", lhs.0.c0.c0);
        println!("[DEBUG] LHS (std e(A,B)):  {:?}", lhs_std.0.c0.c0);
        println!("[DEBUG] e(C_lean, δ): {:?}", pairing_c_delta.0.c0.c0);
        println!("[DEBUG] e(C_std, δ):  {:?}", rhs_std_c.0.c0.c0);
        println!("[DEBUG] R_baked:      {:?}", r_baked.0.c0.c0);
        
        // Compute actual gap at runtime
        let c_gap_runtime = proof_std.c.into_group() - proof_lean.c.into_group();
        let gap_pairing = <DefaultCycle as RecursionCycle>::OuterE::pairing(
            c_gap_runtime.into_affine(),
            vk_outer.delta_g2
        );
        
        // Expected gap from baked target (T_const contribution)
        // T_const = R_baked - R_raw, where R_raw = e(α,β) + e(IC(x), γ)
        let ic_sum = {
            let mut acc = vk_outer.gamma_abc_g1[0].into_group();
            for (i, inp) in inputs_outer.iter().enumerate() {
                acc += vk_outer.gamma_abc_g1[i + 1] * inp;
            }
            acc.into_affine()
        };
        let r_raw = <DefaultCycle as RecursionCycle>::OuterE::pairing(vk_outer.alpha_g1, vk_outer.beta_g2)
            + <DefaultCycle as RecursionCycle>::OuterE::pairing(ic_sum, vk_outer.gamma_g2);
        let t_const_expected = r_baked - r_raw;
        
        println!("[DEBUG] Gap pairing e(C_std - C_lean, δ): {:?}", gap_pairing.0.c0.c0);
        println!("[DEBUG] T_const from baked target:        {:?}", t_const_expected.0.c0.c0);
        println!("[DEBUG] Gap == T_const: {}", gap_pairing == t_const_expected);
        
        // CRITICAL: Check if standard proof verifies with R_raw (without baked correction)
        let std_lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_std.a, proof_std.b);
        let std_rhs = r_raw + rhs_std_c;
        println!("[DEBUG] Standard proof check: e(A,B) == R_raw + e(C,δ): {}", std_lhs == std_rhs);
        
        // Check if standard proof verifies with R_baked
        let std_rhs_baked = r_baked + rhs_std_c;
        println!("[DEBUG] Standard proof with baked: e(A,B) == R_baked + e(C,δ): {}", std_lhs == std_rhs_baked);
        
        // The KEY equation: standard C includes the full quotient, lean C excludes public quotient
        // So: e(C_std, δ) = e(C_lean, δ) + e(Q_const, δ) = e(C_lean, δ) + T_const
        let expected_c_std_pairing = pairing_c_delta + t_const_expected;
        println!("[DEBUG] e(C_std,δ) == e(C_lean,δ) + T_const: {}", rhs_std_c == expected_c_std_pairing);
        
        // Statement info
        println!("[DEBUG] Statement value (x): {:?}", x_inner[0]);
        println!("[DEBUG] Statement as outer field: {:?}", inputs_outer[0]);
        
        // If gap doesn't match T_const, the q_const interpolation is wrong
        if gap_pairing != t_const_expected {
            println!("[ERROR] Gap mismatch! The q_const interpolation failed for statement {:?}", x_inner);
            println!("        This suggests either:");
            println!("        1. H_wit computation in lean prover differs from standard");
            println!("        2. q_const linearity assumption is violated");
            println!("        3. h_query_wit computed with dummy proof differs from real proof");
            
            // Additional diagnostic: check if gap is zero (would mean lean and std C are equal)
            if c_gap_runtime.into_affine().is_zero() {
                println!("[DEBUG] Gap is ZERO - lean C == std C (unexpected!)");
            } else {
                println!("[DEBUG] Gap is NON-ZERO - lean C != std C (expected, but wrong magnitude)");
            }
        }
        
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
    let fixture = get_fixture();

    // Use separate RNG for inner proofs so outer setup RNG stays consistent
    let mut inner_rng = ark_std::rand::rngs::StdRng::seed_from_u64(1234);

    // === STATEMENT 1 ===
    let x_val_1 = InnerScalar::<DefaultCycle>::from(10u64);
    let x_inner_1 = vec![x_val_1];

    // Generate inner proof for statement 1
    let circuit_inner_1 = AddCircuit::with_public_input(x_val_1);
    let proof_inner_1 = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner_1, &mut inner_rng)
        .expect("inner proof 1 failed");

    // === STATEMENT 2 (DIFFERENT) ===
    let x_val_2 = InnerScalar::<DefaultCycle>::from(20u64);
    let x_inner_2 = vec![x_val_2];

    let circuit_inner_2 = AddCircuit::with_public_input(x_val_2);
    let proof_inner_2 = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner_2, &mut inner_rng)
        .expect("inner proof 2 failed");

    // Setup outer circuit
    let circuit_outer_1 = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner_1.clone(),
        proof_inner_1.clone(),
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

    if let Ok((pvugc_vk, lean_pk)) = result {
        // === ARMING ===
        let rho = OuterScalar::<DefaultCycle>::rand(&mut rng);
        let public_inputs_1 = vec![arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner_1[0])];
        let public_inputs_2 = vec![arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner_2[0])];

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
            proof_inner_1.clone(),
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
            proof_inner_1.clone(),
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