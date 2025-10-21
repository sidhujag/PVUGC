//! End-to-End Test for One-Sided GS PVUGC

use arkworks_groth16::*;
use ark_ec::{AffineRepr, pairing::Pairing, PrimeGroup, CurveGroup};
use ark_serialize::CanonicalSerialize;
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ppe::PvugcVk;
use ark_bls12_381::{Bls12_381, Fr};
use ark_std::{UniformRand, rand::rngs::StdRng, rand::SeedableRng};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::alloc::AllocVar;

type E = Bls12_381;

fn ppe_unarmed_assert_full<Ep: ark_ec::pairing::Pairing>(
    x_b_cols: &[(Ep::G1Affine, Ep::G1Affine)],
    pvugc_vk: &arkworks_groth16::ppe::PvugcVk<Ep>,
    theta: &[(Ep::G1Affine, Ep::G1Affine)],
    theta_delta_cancel: &Option<(Ep::G1Affine, Ep::G1Affine)>,
    r_target: ark_ec::pairing::PairingOutput<Ep>,
) {
    use ark_std::One;
    // Y_cols = [beta2] ++ b_g2_query[..]
    let mut y_cols = Vec::with_capacity(1 + pvugc_vk.b_g2_query.len());
    y_cols.push(pvugc_vk.beta_g2);
    y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
    assert_eq!(x_b_cols.len(), y_cols.len(), "|X_B| != |Y|");

    let mut lhs_b = ark_ec::pairing::PairingOutput::<Ep>(One::one());
    for ((x0, x1), y) in x_b_cols.iter().zip(&y_cols) {
        lhs_b += Ep::pairing(*x0, *y);
        if !x1.is_zero() { lhs_b += Ep::pairing(*x1, *y); }
    }
    let mut lhs_delta = ark_ec::pairing::PairingOutput::<Ep>(One::one());
    for (t0, t1) in theta {
        // Expect θ = -C + sA
        lhs_delta += Ep::pairing(*t0, pvugc_vk.delta_g2);
        if !t1.is_zero() { lhs_delta += Ep::pairing(*t1, pvugc_vk.delta_g2); }
    }
    if let Some((c0, c1)) = theta_delta_cancel {
        lhs_delta += Ep::pairing(*c0, pvugc_vk.delta_g2);
        if !c1.is_zero() { lhs_delta += Ep::pairing(*c1, pvugc_vk.delta_g2); }
    }
    let mut lhs = lhs_b;
    lhs += lhs_delta;
    // debug prints removed
    assert_eq!(lhs, r_target, "Unarmed PPE != R(vk,x)");
}


// Test circuit: x = y²
#[derive(Clone)]
struct SquareCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SquareCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        
        Ok(())
    }
}

#[test]
fn test_one_sided_pvugc_proof_agnostic() {
    let mut rng = StdRng::seed_from_u64(0);
    
    
    // Vault setup (statement = public input)
    let vault_utxo = vec![Fr::from(25u64)];  // x = y² = 5² = 25
    
    // Setup Groth16 for the circuit
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    // === DEPOSIT TIME ===
    
    // Build PVUGC VK wrapper
    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    
    // Generate ρ
    let rho = Fr::rand(&mut rng);
    
    // Use the API for setup and arming
    // Column-wise arming
    let (_bases_cols, col_arms, _r, k_expected) = OneSidedPvugc::setup_and_arm(
        &pvugc_vk,
        &vk,
        &vault_utxo,
        &rho,
    );
    
    // === PoCE-A VALIDATION (ARM-TIME) ===
    
    // Generate arming artifacts for PoCE-A
    let s_i = Fr::rand(&mut rng);
    let t_i = (<E as Pairing>::G1::generator() * s_i).into_affine();
    let ctx_hash = b"test_context_hash";
    let gs_digest = b"test_gs_digest";
    
    // Create PoCE-A proof
    let poce_proof = OneSidedPvugc::attest_column_arming(
        &_bases_cols,
        &col_arms,
        &t_i,
        &rho,
        &s_i,
        ctx_hash,
        gs_digest,
        &mut rng,
    );
    
    // Verify PoCE-A proof
    assert!(OneSidedPvugc::verify_column_arming(
        &_bases_cols,
        &col_arms,
        &t_i,
        &poce_proof,
        ctx_hash,
        gs_digest,
    ));
    
    // === SPEND TIME - PROOF 1 ===
    
    // Use coefficient recorder to capture real b_j via HOOKED prover
    let mut recorder1 = SimpleCoeffRecorder::<E>::new();
    let proof1 = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder1).unwrap();
    
    // Use API to build commitments and bundle
    let commitments1 = recorder1.build_commitments();
    let bundle1 = PvugcBundle {
        groth16_proof: proof1.clone(),
        dlrep_b: recorder1.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder1.create_dlrep_tie(&mut rng),
        gs_commitments: commitments1.clone(),
    };
    
    // Verify using OneSidedPvugc (checks PPE equation)
    // Quick unarmed PPE sanity on columns (localizes mapping issues)
    let r_target = compute_groth16_target(&vk, &vault_utxo);
    ppe_unarmed_assert_full::<E>(&commitments1.x_b_cols, &pvugc_vk, &commitments1.theta, &Some(commitments1.theta_delta_cancel), r_target);
    assert!(OneSidedPvugc::verify(&bundle1, &pvugc_vk, &vk, &vault_utxo));
    
    let k1 = OneSidedPvugc::decapsulate(&commitments1, &col_arms);
    
    // === PoCE-B VALIDATION (DECAP-TIME) ===
    
    // Simulate ciphertext
    let ct_i = b"simulated_ciphertext";
    
    // Compute correct key-commitment tag from derived key (matching PoCE-B logic)
    use sha2::{Sha256, Digest};
    
    // Derive KEM key: K = Poseidon2(ser(R^ρ) || ctx_hash || gs_digest)
    let mut key_hasher = Sha256::new();
    let mut key_bytes = Vec::new();
    k1.serialize_compressed(&mut key_bytes).unwrap();
    key_hasher.update(&key_bytes);
    key_hasher.update(ctx_hash);
    key_hasher.update(gs_digest);
    let key = key_hasher.finalize().to_vec();
    
    // Compute key-commitment tag: τ_i = Poseidon2(K, AD_core, ct_i)
    let mut tag_hasher = Sha256::new();
    tag_hasher.update(&key);
    tag_hasher.update(ctx_hash);  // AD_core = ctx_hash
    tag_hasher.update(ct_i);
    let tau_i = tag_hasher.finalize().to_vec();
    
    // Verify key-commitment (PoCE-B)
    assert!(OneSidedPvugc::verify_key_commitment(
        &k1,
        ctx_hash,
        gs_digest,
        ct_i,
        &tau_i,
    ));
    
    // === SPEND TIME - PROOF 2 ===
    
    let mut recorder2 = SimpleCoeffRecorder::<E>::new();
    let proof2 = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder2).unwrap();
    
    // Use API to build commitments and bundle
    let commitments2 = recorder2.build_commitments();
    let bundle2 = PvugcBundle {
        groth16_proof: proof2.clone(),
        dlrep_b: recorder2.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder2.create_dlrep_tie(&mut rng),
        gs_commitments: commitments2.clone(),
    };
    
    // Verify using OneSidedPvugc (checks PPE equation)
    assert!(OneSidedPvugc::verify(&bundle2, &pvugc_vk, &vk, &vault_utxo));
    
    let k2 = OneSidedPvugc::decapsulate(&commitments2, &col_arms);
    
    // === PoCE-B VALIDATION FOR PROOF 2 ===
    
    // Verify key-commitment for second proof (should use same key)
    assert!(OneSidedPvugc::verify_key_commitment(
        &k2,
        ctx_hash,
        gs_digest,
        ct_i,
        &tau_i,
    ));
    
    // === PROOF-AGNOSTIC PROPERTY ===
    
    assert_eq!(k1, k2);
    assert_eq!(k1, k_expected);
    
    
    // === TEST: DIFFERENT STATEMENT PRODUCES DIFFERENT K ===
    
    // Different vault UTXO = different statement = different R
    let vault2_utxo = vec![Fr::from(49u64)];  // x = 7² = 49
    
    // Setup new circuit for x=49
    let circuit2 = SquareCircuit {
        x: Some(Fr::from(49u64)),
        y: Some(Fr::from(7u64)),
    };
    
    let (pk2, vk2) = Groth16::<E>::circuit_specific_setup(circuit2.clone(), &mut rng).unwrap();
    let pvugc_vk2 = PvugcVk {
        beta_g2: vk2.beta_g2,
        delta_g2: vk2.delta_g2,
        b_g2_query: pk2.b_g2_query.clone(),
    };
    
    // Generate proof for vault 2
    let mut recorder_vault2 = SimpleCoeffRecorder::<E>::new();
    let proof_vault2 = Groth16::<E>::create_random_proof_with_hook(
        circuit2, &pk2, &mut rng, &mut recorder_vault2
    ).unwrap();
    
    // Build commitments/bundle for vault 2
    let commitments_vault2 = recorder_vault2.build_commitments();
    let bundle_vault2 = PvugcBundle {
        groth16_proof: proof_vault2.clone(),
        dlrep_b: recorder_vault2.create_dlrep_b(&pvugc_vk2, &mut rng),
        dlrep_tie: recorder_vault2.create_dlrep_tie(&mut rng),
        gs_commitments: commitments_vault2.clone(),
    };
    
    // VERIFY vault2's bundle
    assert!(OneSidedPvugc::verify(&bundle_vault2, &pvugc_vk2, &vk2, &vault2_utxo));
    
    // Setup column arms for vault 2 (SAME ρ, different VK)
    let (_bases_cols2, col_arms2, _r2, _k2_expected_from_setup) = OneSidedPvugc::setup_and_arm(
        &pvugc_vk2,
        &vk2,
        &vault2_utxo,
        &rho,
    );
    
    // Decap vault2's proof via column path
    let k_vault2_decap = OneSidedPvugc::decapsulate(&commitments_vault2, &col_arms2);
    
    // Compute expected R for vault 2
    let r_vault2 = compute_groth16_target(&vk2, &vault2_utxo);
    let k_vault2_expected = OneSidedPvugc::compute_r_to_rho(&r_vault2, &rho);
    
    // Verify vault2 decap matches its expected R^ρ
    assert_eq!(k_vault2_decap, k_vault2_expected, "Vault2 decap should match R₂^ρ");
    
    // Different statements should produce different K
    // Even though we use SAME ρ!
    assert_ne!(k1, k_vault2_decap, "Different vaults MUST produce different keys!");
}

#[test]
fn test_delta_sign_sanity() {
    let mut rng = StdRng::seed_from_u64(42);
    let vault_utxo = vec![Fr::from(25u64)];
    let circuit = SquareCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    let rho = Fr::rand(&mut rng);
    
    // Use API for setup and arming
    let (_bases_cols, col_arms, _r, k_expected) = OneSidedPvugc::setup_and_arm(
        &pvugc_vk,
        &vk,
        &vault_utxo,
        &rho,
    );

    // Hooked proof and commitments
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder).unwrap();
    assert!(Groth16::<E>::verify(&vk, &vault_utxo, &proof).unwrap());
    
    let commitments = recorder.build_commitments();

    // Correct sign → K_good == R^ρ
    let k_good = OneSidedPvugc::decapsulate(&commitments, &col_arms);
    assert_eq!(k_good, k_expected);
}

#[test]
fn test_r_computation_deterministic() {
    let mut rng = StdRng::seed_from_u64(1);
    
    
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    let vault_utxo = vec![Fr::from(12345u64)];
    
    // Compute R twice
    let r1 = compute_groth16_target(&vk, &vault_utxo);
    let r2 = compute_groth16_target(&vk, &vault_utxo);
    
    assert_eq!(r1, r2);
}

#[test]
fn test_different_vaults_different_r() {
    let mut rng = StdRng::seed_from_u64(2);
    
    
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    
    let vault1 = vec![Fr::from(12345u64)];
    let vault2 = vec![Fr::from(67890u64)];
    
    let r1 = compute_groth16_target(&vk, &vault1);
    let r2 = compute_groth16_target(&vk, &vault2);
    
    assert_ne!(r1, r2);
}

#[test]
fn test_witness_independence() {
    use ark_std::UniformRand;
    
    let mut rng = StdRng::seed_from_u64(300);
    
    
    // Addition circuit
    #[derive(Clone)]
    struct AddCircuit {
        pub x: Option<Fr>,
        pub y: Option<Fr>,
        pub z: Option<Fr>,
    }
    
    impl ConstraintSynthesizer<Fr> for AddCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let x_var = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
            let y_var = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
            let z_var = FpVar::new_witness(cs.clone(), || self.z.ok_or(SynthesisError::AssignmentMissing))?;
            let sum = &y_var + &z_var;
            x_var.enforce_equal(&sum)?;
            Ok(())
        }
    }
    
    let public_x = vec![Fr::from(11u64)];
    
    // Witness 1: y=4, z=7 (4+7=11)
    let circuit1 = AddCircuit {
        x: Some(public_x[0]),  // Use public_x
        y: Some(Fr::from(4u64)),
        z: Some(Fr::from(7u64)),
    };
    
    // Witness 2: y=5, z=6 (5+6=11)
    let circuit2 = AddCircuit {
        x: Some(public_x[0]),  // Same public_x
        y: Some(Fr::from(5u64)),
        z: Some(Fr::from(6u64)),
    };
    
    // ONE setup (same pk, vk for both witnesses)
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit1.clone(), &mut rng).unwrap();
    
    // Compute R = e(α,β)·e(L(x),γ) from (vk, public_x)
    let r_statement = compute_groth16_target(&vk, &public_x);
    
    
    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: pk.b_g2_query.clone(),
    };
    
    let rho = Fr::rand(&mut rng);
    
    let (_, col_arms, _, k_expected) = OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &public_x, &rho);
    
    let mut recorder1 = SimpleCoeffRecorder::<E>::new();
    let proof1 = Groth16::<E>::create_random_proof_with_hook(circuit1, &pk, &mut rng, &mut recorder1).unwrap();
    
    let commitments1 = recorder1.build_commitments();
    let bundle1 = PvugcBundle {
        groth16_proof: proof1,
        dlrep_b: recorder1.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder1.create_dlrep_tie(&mut rng),
        gs_commitments: commitments1.clone(),
    };
    
    assert!(OneSidedPvugc::verify(&bundle1, &pvugc_vk, &vk, &public_x));
    let k1 = OneSidedPvugc::decapsulate(&commitments1, &col_arms);
    
    let mut recorder2 = SimpleCoeffRecorder::<E>::new();
    let proof2 = Groth16::<E>::create_random_proof_with_hook(circuit2, &pk, &mut rng, &mut recorder2).unwrap();
    
    let commitments2 = recorder2.build_commitments();
    let bundle2 = PvugcBundle {
        groth16_proof: proof2,
        dlrep_b: recorder2.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder2.create_dlrep_tie(&mut rng),
        gs_commitments: commitments2.clone(),
    };
    
    assert!(OneSidedPvugc::verify(&bundle2, &pvugc_vk, &vk, &public_x));
    let k2 = OneSidedPvugc::decapsulate(&commitments2, &col_arms);
    
    // Since R = compute_groth16_target(vk, public_x) doesn't use witnesses:
    // R is the SAME for both proofs
    assert_eq!(k1, k2, "WITNESS-INDEPENDENT: Different witnesses → Same K!");
    
    // Verify both equal expected R^ρ (from statement)
    let k_expected_r = OneSidedPvugc::compute_r_to_rho(&r_statement, &rho);
    assert_eq!(k1, k_expected_r, "K₁ should equal R^ρ");
    assert_eq!(k2, k_expected_r, "K₂ should equal R^ρ");
    assert_eq!(k1, k_expected, "Should match setup_and_arm");
    
}
