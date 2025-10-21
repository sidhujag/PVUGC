//! Security Tests for One-Sided GS PVUGC

use arkworks_groth16::*;
use arkworks_groth16::ppe::PvugcVk;
use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
use ark_std::{UniformRand, rand::rngs::StdRng, rand::SeedableRng};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::alloc::AllocVar;
use ark_ec::{CurveGroup, AffineRepr, pairing::PairingOutput};

type E = Bls12_381;

#[derive(Clone)]
struct TestCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y_var = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        Ok(())
    }
}

#[test]
fn test_cannot_compute_k_from_arms_alone() {
    let mut rng = StdRng::seed_from_u64(10);
    
    let circuit = TestCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    
    let vault_utxo = vec![Fr::from(25u64)];
    
    // Compute R
    let r = compute_groth16_target(&vk, &vault_utxo);
    
    // Build column bases and arm them
    let rho = Fr::rand(&mut rng);
    let pvugc_vk: PvugcVk<E> = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    let mut y_cols = vec![pvugc_vk.beta_g2];
    y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
    let cols: ColumnBases<E> = ColumnBases { y_cols, delta: pvugc_vk.delta_g2 };
    let col_arms = arm_columns(&cols, &rho);
    
    // Expected K = R^ρ
    let k_expected = OneSidedPvugc::compute_r_to_rho(&r, &rho);
    
    // Create random fake commitments (not derived from valid proof)
    use ark_std::test_rng;
    let mut rng_fake = test_rng();
    let fake_x_b_cols: Vec<_> = cols
        .y_cols
        .iter()
        .map(|_| (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)))
        .collect();
    let fake_theta = vec![(G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake))];
    let fake_commitments: OneSidedCommitments<E> = OneSidedCommitments { 
        x_b_cols: fake_x_b_cols, 
        theta: fake_theta, 
        theta_delta_cancel: (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)) 
    };
    
    // Security property: fake commitments + valid arms should NOT produce correct K
    let fake_k = OneSidedPvugc::decapsulate(&fake_commitments, &col_arms);
    assert_ne!(fake_k, k_expected, "Fake commitments should not produce correct K = R^ρ");
    
    // Additional check: fake K should not be identity (trivial case)
    use ark_std::One;
    assert_ne!(fake_k, PairingOutput::<E>(One::one()), "Fake K should not be identity");
}

#[test]
fn test_invalid_groth16_rejected() {
    let mut rng = StdRng::seed_from_u64(3);
    
    
    let circuit = TestCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    
    let vault_utxo = vec![Fr::from(25u64)];
    
    // Create random invalid proof
    let invalid_proof = ark_groth16::Proof {
        a: G1Affine::rand(&mut rng),
        b: G2Affine::rand(&mut rng),
        c: G1Affine::rand(&mut rng),
    };
    
    // Verify should fail
    let valid = Groth16::<E>::verify(&vk, &vault_utxo, &invalid_proof).unwrap_or(false);
    
    assert!(!valid);
}


#[test]
fn test_dlrep_detects_wrong_coefficients() {
    let mut rng = StdRng::seed_from_u64(12);
    
    
    let y_bases = vec![G2Affine::rand(&mut rng); 2];
    let delta = G2Affine::rand(&mut rng);
    
    // Honest coefficients
    let b_honest = vec![Fr::from(2u64), Fr::from(3u64)];
    let s = Fr::from(7u64);
    
    // Compute B with honest coefficients
    let mut b_honest_g2 = delta.into_group() * s;
    for (b_j, y_j) in b_honest.iter().zip(&y_bases) {
        b_honest_g2 += y_j.into_group() * b_j;
    }
    let b_honest_g2 = b_honest_g2.into_affine();
    
    // Create proof with honest coefficients
    let proof: DlrepBProof<E> = prove_b_msm(b_honest_g2, &y_bases, delta, &b_honest, s, &mut rng);
    
    // Try to verify against WRONG B
    let b_wrong = G2Affine::rand(&mut rng);
    let valid = verify_b_msm(b_wrong, &y_bases, delta, &proof);
    
    assert!(!valid);
}

#[test]
fn test_different_witnesses_same_statement() {
    
    // Same circuit, different witnesses
    let circuit1 = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),   // Witness 1: y = 5
    };
    
    let circuit2 = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),   // Witness 2: same value (for x=25, only y=±5 works)
    };
    
    let mut rng_crypto = StdRng::seed_from_u64(5);
    let (_pk1, vk1) = Groth16::<E>::circuit_specific_setup(circuit1, &mut rng_crypto).unwrap();
    let (_pk2, vk2) = Groth16::<E>::circuit_specific_setup(circuit2, &mut rng_crypto).unwrap();
    
    let vault_utxo = vec![Fr::from(25u64)];
    
    let _r1 = compute_groth16_target(&vk1, &vault_utxo);
    let _r2 = compute_groth16_target(&vk2, &vault_utxo);
    
    
}

#[test]
fn test_verify_rejects_mismatched_statement() {
    let mut rng = StdRng::seed_from_u64(13);

    let circuit = TestCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    let vault_utxo = vec![Fr::from(25u64)];
    let wrong_vault_utxo = vec![Fr::from(49u64)];

    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };

    // Canonical Γ required by verifier

    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder).unwrap();

    let commitments = recorder.build_commitments();
    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder.create_dlrep_tie(&mut rng),
        gs_commitments: commitments,
    };

    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &vault_utxo));
    assert!(!OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &wrong_vault_utxo));
}

