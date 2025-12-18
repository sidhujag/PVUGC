//! SP1 End-to-End Integration Test
//!
//! This test demonstrates the full flow:
//! 1. SP1 generates a Groth16 proof (using our BLS12-377 fork)
//! 2. sp1_bridge deserializes and computes armed_digest
//! 3. Outer circuit verifies the inner proof
//! 4. PVUGC decap extracts the key
//!
//! **Architecture:**
//! - SP1 SDK generates proofs (calls gnark internally)
//! - sp1_bridge deserializes gnark output → arkworks types
//! - Outer circuit wraps the SP1 proof on BW6-761

use ark_bls12_377::{Bls12_377, Fr as Fr377};
use ark_ff::{PrimeField, UniformRand};
use ark_groth16::Proof;
use ark_std::rand::SeedableRng;
use ark_std::rand::rngs::StdRng;

use sp1_sdk::{ProverClient, SP1Stdin, HashableKey, Prover};
use sp1_sdk::install::try_install_circuit_artifacts;

use arkworks_groth16::sp1_bridge::{
    Sp1PublicInputs,
    decode_sp1_proof_hex,
    decode_sp1_public_input,
    parse_gnark_proof_bls12_377, parse_gnark_vk_bls12_377,
};
use arkworks_groth16::outer_compressed::{
    Bls12Bw6Cycle, OuterCircuit, RecursionCycle, OuterScalar,
    setup_outer_params_for, fr_inner_to_outer_for,
};

/// Simple fibonacci program for SP1
/// This is the ELF binary that SP1 will execute and prove
const FIBONACCI_ELF: &[u8] = test_artifacts::FIBONACCI_ELF;
const SSZ_WITHDRAWALS_ELF: &[u8] = test_artifacts::SSZ_WITHDRAWALS_ELF;
const TENDERMINT_ELF: &[u8] = test_artifacts::TENDERMINT_ELF;

#[test]
#[ignore] // Run with: cargo test test_sp1_fibonacci_mock -- --ignored
fn test_sp1_fibonacci_mock() {
    println!("\n=== SP1 Fibonacci Mock Test ===\n");
    
    // Create SP1 mock prover (no actual proof generation)
    let client = ProverClient::builder().mock().build();
    
    // Setup input
    let mut stdin = SP1Stdin::new();
    stdin.write(&10u32); // Compute fib(10)
    
    // Execute program in mock mode
    println!("Executing SP1 program (mock mode)...");
    let (_pk, vk) = client.setup(FIBONACCI_ELF);
    
    // Execute to get public values
    let (public_values, _) = client.execute(FIBONACCI_ELF, &stdin).run().expect("execution failed");
    println!("  ✓ Program executed");
    println!("  Public values: {:?}", public_values.as_slice());
    let vk_hash: String = vk.bytes32();
    println!("  VKey hash: {}", vk_hash);
    
    // In mock mode, we can verify the execution completed correctly
    // Real Groth16 proving would require: client.prove(&pk, &stdin).groth16().run()
    println!("\n  Note: For actual Groth16 proof, use prover network or run with:");
    println!("    SP1_PROVER=network cargo test test_sp1_fibonacci_groth16 -- --ignored");
}

#[test]
#[ignore] // Run with: SP1_PROVER=network cargo test test_sp1_fibonacci_groth16 -- --ignored
fn test_sp1_fibonacci_groth16() {
    println!("\n=== SP1 Fibonacci Groth16 Proof Test ===\n");
    
    // Create SP1 prover from environment (network or local)
    let client = ProverClient::from_env();
    
    // Setup input
    let mut stdin = SP1Stdin::new();
    stdin.write(&10u32); // Compute fib(10)
    
    // Generate proof
    println!("Generating SP1 Groth16 proof...");
    let (pk, vk) = client.setup(FIBONACCI_ELF);
    let proof = client.prove(&pk, &stdin).groth16().run().expect("proving failed");
    
    println!("  ✓ SP1 proof generated");
    println!("  VKey hash: {}", vk.bytes32());
    
    // Get raw proof bytes for bridge
    let raw_proof = proof.bytes();
    println!("  Raw proof size: {} bytes", raw_proof.len());
    
    // Verify with SP1
    client.verify(&proof, &vk).expect("verification failed");
    println!("  ✓ SP1 verification passed");
}

/// Full E2E test with simulated inner proof
/// This test verifies the full PVUGC pipeline works with SP1's proof structure
#[test]
fn test_sp1_to_pvugc_simulated() {
    use arkworks_groth16::pvugc_outer::{
        build_pvugc_setup_from_pk_for,
        build_column_bases_outer_for,
        arm_columns_outer_for,
        compute_target_outer_for,
        compute_r_to_rho_outer_for,
    };
    use arkworks_groth16::prover_lean::prove_lean_with_randomizers;
    use arkworks_groth16::decap::build_commitments;
    use arkworks_groth16::ct::gt_eq_ct;
    use ark_groth16::Groth16;
    use ark_snark::SNARK;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    
    println!("\n=== SP1 → PVUGC Simulated E2E Test (2 public inputs) ===\n");
    
    let mut rng = StdRng::seed_from_u64(42);
    type Cycle = Bls12Bw6Cycle;
    
    // Step 1: Create a mock "inner" circuit that mimics SP1's structure
    // SP1's Groth16 wrapper has 2 public inputs: vkey_hash, committed_values_digest
    #[derive(Clone)]
    struct MockSp1InnerCircuit {
        vkey_hash: Option<Fr377>,
        committed_values_digest: Option<Fr377>,
    }
    
    impl ConstraintSynthesizer<Fr377> for MockSp1InnerCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr377>) -> Result<(), SynthesisError> {
            use ark_r1cs_std::prelude::*;
            use ark_r1cs_std::fields::fp::FpVar;
            
            // SP1's 2 public inputs
            let vkey_hash = FpVar::new_input(cs.clone(), || {
                self.vkey_hash.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let committed_values_digest = FpVar::new_input(cs.clone(), || {
                self.committed_values_digest.ok_or(SynthesisError::AssignmentMissing)
            })?;
            
            // Add some constraints to simulate SP1's wrapper (simplified)
            let sum = &vkey_hash + &committed_values_digest;
            let _ = &sum * &sum; // Just to have some constraints
            
            Ok(())
        }
    }
    
    println!("Step 1: Setting up mock SP1 inner circuit (2 public inputs)...");
    
    // SP1's actual public inputs (no hashing needed!)
    let vkey_hash = Fr377::from(67890u64);     // SP1 program's vkey hash
    let committed_values_digest = Fr377::from(11111u64); // Program outputs
    
    let inner_circuit = MockSp1InnerCircuit {
        vkey_hash: Some(vkey_hash),
        committed_values_digest: Some(committed_values_digest),
    };
    
    // Generate inner keys and proof
    let (inner_pk, inner_vk) = Groth16::<Bls12_377>::circuit_specific_setup(
        inner_circuit.clone(),
        &mut rng,
    ).expect("inner setup failed");
    
    let inner_proof = Groth16::<Bls12_377>::prove(&inner_pk, inner_circuit.clone(), &mut rng)
        .expect("inner prove failed");
    
    // Verify inner proof with 2 public inputs
    let inner_public_inputs = vec![vkey_hash, committed_values_digest];
    assert!(
        Groth16::<Bls12_377>::verify(&inner_vk, &inner_public_inputs, &inner_proof).unwrap(),
        "Inner proof verification failed"
    );
    println!("  ✓ Mock inner proof generated and verified");
    println!("  vkey_hash: {:?}", vkey_hash);
    println!("  committed_values_digest: {:?}", committed_values_digest);
    
    // Step 2: Setup outer circuit
    println!("\nStep 2: Setting up outer circuit...");
    let (pk_outer, vk_outer) = setup_outer_params_for::<Cycle>(
        &inner_vk,
        inner_public_inputs.len(),
        &mut rng,
    ).expect("outer setup failed");
    
    // Create inner proof generator for PVUGC setup
    let inner_proof_for_gen = inner_proof.clone();
    let inner_proof_generator = move |_x: &[Fr377]| -> Proof<Bls12_377> {
        inner_proof_for_gen.clone()
    };
    
    let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for::<Cycle, _>(
        &pk_outer,
        &inner_vk,
        inner_proof_generator,
    );
    println!("  ✓ Outer circuit setup complete");
    
    // Step 3: Generate outer proof
    println!("\nStep 3: Generating outer proof...");
    let circuit = OuterCircuit::<Cycle>::new(
        inner_vk.clone(),
        inner_public_inputs.clone(),
        inner_proof.clone(),
    );
    
    let r = OuterScalar::<Cycle>::rand(&mut rng);
    let s = OuterScalar::<Cycle>::rand(&mut rng);
    
    let (proof_outer, assignment) = prove_lean_with_randomizers(&lean_pk, circuit, r, s)
        .expect("lean prove failed");
    println!("  ✓ Outer proof generated");
    
    // Step 4: PVUGC decap
    println!("\nStep 4: PVUGC decapsulation...");
    
    let x_outer: Vec<OuterScalar<Cycle>> = inner_public_inputs
        .iter()
        .map(|x| fr_inner_to_outer_for::<Cycle>(x))
        .collect();
    
    let bases = build_column_bases_outer_for::<Cycle>(&pvugc_vk, &vk_outer, &x_outer);
    let rho = OuterScalar::<Cycle>::rand(&mut rng);
    let col_arms = arm_columns_outer_for::<Cycle>(&bases, &rho);
    
    let num_instance = vk_outer.gamma_abc_g1.len();
    let commitments = build_commitments::<<Cycle as RecursionCycle>::OuterE>(
        &proof_outer.a,
        &proof_outer.c,
        &s,
        &assignment,
        num_instance,
    );
    
    let k_decapped = arkworks_groth16::decap::decap(&commitments, &col_arms)
        .expect("decap failed");
    
    let r_target = compute_target_outer_for::<Cycle>(&vk_outer, &pvugc_vk, &inner_public_inputs);
    let k_expected = compute_r_to_rho_outer_for::<Cycle>(&r_target, &rho);
    
    assert!(
        gt_eq_ct::<<Cycle as RecursionCycle>::OuterE>(&k_decapped, &k_expected),
        "Decapped key doesn't match expected R^ρ!"
    );
    println!("  ✓ K_decapped == R^ρ verified!");
    
    println!("\n=== SP1 → PVUGC Simulated E2E Test PASSED ===");
}

#[test]
#[ignore] // Run with: SP1_PROVER=network cargo test test_sp1_to_pvugc_real -- --ignored
fn test_sp1_to_pvugc_real() {
    use ark_ec::pairing::Pairing;
    use ark_ff::BigInteger;
    use ark_groth16::{prepare_verifying_key, Groth16};
    use arkworks_groth16::ppe::compute_baked_target;
    use arkworks_groth16::prover_lean::prove_lean_with_randomizers;
    use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for_with_samples;
    use arkworks_groth16::pvugc_outer::{
        arm_columns_outer_for, build_column_bases_outer_for, compute_r_to_rho_outer_for,
        compute_target_outer_for,
    };
    use arkworks_groth16::decap::build_commitments;
    use arkworks_groth16::ct::gt_eq_ct;
    use std::collections::HashMap;

    println!("\n=== SP1 → PVUGC Real E2E Test (Lean verify, quotient-gap setup) ===\n");
    
    // Compatibility: older SP1 guest ELFs may still use deprecated file descriptors
    // (e.g. fd=3 for public values) which are rejected by SP1 >= v4 unless explicitly allowed.
    // This is test-only to keep CI/dev flows working while ELFs are refreshed.
    std::env::set_var("SP1_ALLOW_DEPRECATED_HOOKS", "true");
    
    let mut rng = StdRng::seed_from_u64(42);
    type Cycle = Bls12Bw6Cycle;

    // Step 1: Generate N=3 real SP1 Groth16 proofs to provide n+1 samples for quotient-gap setup
    // (here n=2 public inputs → need 3 samples). These proofs are ONLY used to compute the
    // standard–lean C-gap (q_const). They are not the "runtime" proof we verify end-to-end.
    println!("Step 1: Generating 4 different SP1 Groth16 proofs (3 setup samples for quotient-gap and 1 runtime proof)...");
    let client = ProverClient::from_env();
    
    // Two different programs → different SP1 program vk/pk (and critically different vkey_hash),
    // while the Groth16 wrapper VK remains shared for a fixed SP1 build/config.
    let (pk_fib, vk_fib) = client.setup(FIBONACCI_ELF);
    let (pk_ssz, vk_ssz) = client.setup(SSZ_WITHDRAWALS_ELF);
    let (pk_tendermint, vk_tendermint) = client.setup(TENDERMINT_ELF);

    let mut stdin_1 = SP1Stdin::new();
    stdin_1.write(&10u32);
    let sp1_sample_1 = client
        .prove(&pk_fib, &stdin_1)
        .groth16()
        .run()
        .expect("sample proving #1 (fib) failed");

    let mut stdin_2 = SP1Stdin::new();
    stdin_2.write(&11u32);
    let sp1_sample_2 = client
        .prove(&pk_fib, &stdin_2)
        .groth16()
        .run()
        .expect("sample proving #2 (fib) failed");

    // Third sample comes from a DIFFERENT program so vkey_hash differs, ensuring the
    // (n+1)x(n+1) sample matrix is invertible for n=2.
    let stdin_3: SP1Stdin = bincode::deserialize(test_artifacts::SSZ_WITHDRAWALS_INPUT_BIN)
        .expect("deserialize ssz-withdrawals stdin");
    let sp1_sample_3 = client
        .prove(&pk_ssz, &stdin_3)
        .groth16()
        .run()
        .expect("sample proving #3 (ssz-withdrawals) failed");

    println!("  ✓ SP1 setup-sample proofs generated (3 samples)");
    println!("  Program vkey_hash (fib): {}", vk_fib.bytes32());
    println!("  Program vkey_hash (ssz-withdrawals): {}", vk_ssz.bytes32());
    println!("  Program vkey_hash (tendermint runtime): {}", vk_tendermint.bytes32());
    
    // Step 2: Bridge to arkworks
    println!("\nStep 2: Bridging to arkworks...");

    // Load the Groth16 verifying key from the *same artifacts dir SP1 used*.
    let artifacts_dir = match std::env::var("SP1_DEV") {
        Ok(v) if v == "1" || v.eq_ignore_ascii_case("true") => {
            // In dev mode, SP1 builds wrapper artifacts into ~/.sp1/circuits/dev.
            let home = std::env::var_os("HOME")
                .or_else(|| std::env::var_os("USERPROFILE"))
                .expect("HOME/USERPROFILE must be set to locate ~/.sp1");
            std::path::PathBuf::from(home).join(".sp1").join("circuits").join("dev")
        }
        _ => try_install_circuit_artifacts("groth16"),
    };
 

    let groth16_vk_path = artifacts_dir.join("groth16_vk.bin");
    let vk_bytes = std::fs::read(&groth16_vk_path).unwrap_or_else(|e| {
        panic!("read groth16_vk.bin at {}: {e}", groth16_vk_path.display())
    });
    let inner_vk = parse_gnark_vk_bls12_377(&vk_bytes).expect("parse gnark raw vk");
    let inner_pvk = prepare_verifying_key(&inner_vk);

    // Helper: map statement -> bridged inner proof for the sampled statements only.
    let stmt_key = |s: &[Fr377]| -> Vec<u8> {
        s.iter().flat_map(|x| x.into_bigint().to_bytes_le()).collect()
    };

    let bridge_sp1 = |label: &str, proof: &sp1_sdk::SP1Proof| -> (Vec<Fr377>, Proof<Bls12_377>) {
        let (raw_proof_hex, public_inputs_hex) = match proof {
            sp1_sdk::SP1Proof::Groth16(p) => (p.raw_proof.clone(), p.public_inputs.clone()),
            other => panic!("expected Groth16 proof, got {other}"),
        };

        let proof_bytes = decode_sp1_proof_hex(&raw_proof_hex).expect("decode raw_proof hex");
        let inner_proof = parse_gnark_proof_bls12_377(&proof_bytes).expect("parse gnark raw proof");

        // Decode SP1's two public inputs (Fr377).
        let vkey_hash_fe = decode_sp1_public_input(&public_inputs_hex[0]).expect("decode vkey_hash");
        let committed_values_digest_fe =
            decode_sp1_public_input(&public_inputs_hex[1]).expect("decode committed_values_digest");
        let statement = vec![vkey_hash_fe, committed_values_digest_fe];

        // Sanity: ensure the bridged proof is actually valid under arkworks for this VK + statement.
        assert!(
            Groth16::<Bls12_377>::verify_proof(&inner_pvk, &inner_proof, &statement).unwrap(),
            "[{label}] bridged gnark proof failed arkworks verification"
        );
        (statement, inner_proof)
    };

    let (s1, p1) = bridge_sp1("sample#1", &sp1_sample_1.proof);
    let (s2, p2) = bridge_sp1("sample#2", &sp1_sample_2.proof);
    let (s3, p3) = bridge_sp1("sample#3", &sp1_sample_3.proof);

    // Step 3: Outer setup (Groth16 over BW6-761) + PVUGC lean setup (computes quotient gap)
    println!("\nStep 3: Outer setup + PVUGC lean setup (compute q_const from gap)...");
    let (pk_outer, vk_outer) =
        setup_outer_params_for::<Cycle>(&inner_vk, /*num_inner_public_inputs=*/ 2, &mut rng)
            .expect("outer setup failed");

    let mut proof_by_stmt: HashMap<Vec<u8>, Proof<Bls12_377>> = HashMap::new();
    proof_by_stmt.insert(stmt_key(&s1), p1.clone());
    proof_by_stmt.insert(stmt_key(&s2), p2.clone());
    proof_by_stmt.insert(stmt_key(&s3), p3.clone());

    let sample_statements = vec![s1.clone(), s2.clone(), s3.clone()];
    let inner_proof_generator = move |statement: &[Fr377]| -> Proof<Bls12_377> {
        let k = stmt_key(statement);
        proof_by_stmt
            .get(&k)
            .cloned()
            .unwrap_or_else(|| panic!("no cached inner proof for requested statement (len={})", statement.len()))
    };

    let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for_with_samples::<Cycle, _>(
        &pk_outer,
        &inner_vk,
        inner_proof_generator,
        sample_statements,
    );
    println!("  ✓ PVUGC lean setup complete");

    // Step 4: Prove outer with Lean prover and verify with baked target (no standard Groth16 verify here).
    println!("\nStep 4: Lean-prove outer circuit for runtime SP1 statement and verify full pipeline (baked target + PVUGC decap)...");

    // Runtime statement (arming-time): compute from non-proof data (program VK + public values),
    // then arm BEFORE producing any runtime proof.
    let stdin_rt: SP1Stdin =
        bincode::deserialize(test_artifacts::TENDERMINT_INPUT_BIN).expect("deserialize tendermint stdin");
    let (public_values_rt, _report_rt) = client
        .execute(TENDERMINT_ELF, &stdin_rt)
        .run()
        .expect("tendermint execute failed");
    let vkey_hash_rt = pk_tendermint.vk.hash_bn254().as_canonical_biguint().to_string();
    let committed_values_digest_rt = public_values_rt.hash_bn254().to_string();
    let s_rt = vec![
        decode_sp1_public_input(&vkey_hash_rt).expect("decode runtime vkey_hash"),
        decode_sp1_public_input(&committed_values_digest_rt).expect("decode runtime committed_values_digest"),
    ];

    // Arm once for the runtime statement. In PVUGC this simulates the deposit-side arming.
    let rho = OuterScalar::<Cycle>::rand(&mut rng);
    let public_inputs_outer_rt: Vec<OuterScalar<Cycle>> =
        s_rt.iter().map(|x| fr_inner_to_outer_for::<Cycle>(x)).collect();
    let bases_rt = build_column_bases_outer_for::<Cycle>(&pvugc_vk, &vk_outer, &public_inputs_outer_rt);
    let col_arms_rt = arm_columns_outer_for::<Cycle>(&bases_rt, &rho);

    // Expected extracted key for runtime statement: K = R(vk,x)^ρ.
    let r_target_rt = compute_target_outer_for::<Cycle>(&vk_outer, &pvugc_vk, &s_rt);
    let k_expected_rt = compute_r_to_rho_outer_for::<Cycle>(&r_target_rt, &rho);

    // Now produce the runtime proof (after arming).
    let sp1_runtime = client
        .prove(&pk_tendermint, &stdin_rt)
        .groth16()
        .run()
        .expect("runtime proving (tendermint) failed");
    println!("  ✓ SP1 runtime proof generated (tendermint)");
    let (s_rt_from_proof, p_rt) = bridge_sp1("runtime", &sp1_runtime.proof);
    assert_eq!(
        s_rt_from_proof, s_rt,
        "runtime proof public inputs must match the pre-armed statement"
    );

    let mut prove_verify_and_decap =
        |label: &str, statement: &[Fr377], inner_proof: &Proof<Bls12_377>| {
            let circuit = OuterCircuit::<Cycle>::new(inner_vk.clone(), statement.to_vec(), inner_proof.clone());
            let r = OuterScalar::<Cycle>::rand(&mut rng);
            let s = OuterScalar::<Cycle>::rand(&mut rng);
            let (proof_outer_lean, assignment) =
                prove_lean_with_randomizers(&lean_pk, circuit, r, s).expect("lean proving failed");

            let public_inputs_outer: Vec<OuterScalar<Cycle>> =
                statement.iter().map(|x| fr_inner_to_outer_for::<Cycle>(x)).collect();
            let r_baked = compute_baked_target(&vk_outer, &pvugc_vk, &public_inputs_outer)
                .expect("compute baked target");

            let lhs = <Cycle as RecursionCycle>::OuterE::pairing(proof_outer_lean.a, proof_outer_lean.b);
            let rhs =
                r_baked + <Cycle as RecursionCycle>::OuterE::pairing(proof_outer_lean.c, vk_outer.delta_g2);
            assert_eq!(lhs, rhs, "[{label}] Lean outer proof failed baked-target verification");

            // PVUGC decap: extract K = R^ρ from the outer proof using armed bases.
            let num_instance = vk_outer.gamma_abc_g1.len();
            let commitments = build_commitments::<<Cycle as RecursionCycle>::OuterE>(
                &proof_outer_lean.a,
                &proof_outer_lean.c,
                &s,
                &assignment,
                num_instance,
            );
            let k_decapped =
                arkworks_groth16::decap::decap(&commitments, &col_arms_rt).expect("decap failed");
            assert!(
                gt_eq_ct::<<Cycle as RecursionCycle>::OuterE>(&k_decapped, &k_expected_rt),
                "[{label}] decapped key mismatch: expected R^rho for runtime statement"
            );

            println!("  ✓ [{label}] Lean outer proof verified (baked target) + PVUGC decap ok");
            k_decapped
        };

    // Runtime: verify the actual proof we want to connect to the outer circuit.
    let k1 = prove_verify_and_decap("runtime#1", &s_rt, &p_rt);
    // And show a second outer proof for the same runtime statement verifies too (fresh outer randomness).
    let k2 = prove_verify_and_decap("runtime#2", &s_rt, &p_rt);
    assert!(
        gt_eq_ct::<<Cycle as RecursionCycle>::OuterE>(&k1, &k2),
        "proof-agnostic decap failed: two outer proofs for same statement should decap to same key"
    );

    println!("\n=== SP1 → PVUGC Real E2E Test (Lean verify) PASSED ===");
}

#[test]
fn test_sp1_public_inputs() {
    println!("\n=== SP1 Public Inputs Test ===\n");
    
    // SP1's 2 public inputs - no hashing needed, PVUGC handles both directly
    let vkey_hash_1 = Fr377::from(100u64);
    let vkey_hash_2 = Fr377::from(200u64);
    let claim_1 = Fr377::from(1000u64);
    let claim_2 = Fr377::from(2000u64);
    
    let inputs_1 = Sp1PublicInputs::new(vkey_hash_1, claim_1);
    let inputs_2 = Sp1PublicInputs::new(vkey_hash_2, claim_1);
    let inputs_3 = Sp1PublicInputs::new(vkey_hash_1, claim_2);
    
    // Different inputs should produce different vectors
    assert_ne!(inputs_1.to_vec(), inputs_2.to_vec(), "Different vkey_hash should differ");
    assert_ne!(inputs_1.to_vec(), inputs_3.to_vec(), "Different claim should differ");
    
    // Test as_slice
    let slice = inputs_1.as_slice();
    assert_eq!(slice[0], vkey_hash_1);
    assert_eq!(slice[1], claim_1);
    
    // Test to_vec produces correct length (2 elements)
    assert_eq!(inputs_1.to_vec().len(), 2);
    
    println!("✓ Sp1PublicInputs correctly handles 2 public inputs");
    println!("  - vkey_hash: identifies SP1 program");
    println!("  - committed_values_digest: binds program outputs");
}
