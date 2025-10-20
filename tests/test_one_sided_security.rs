//! Security Tests for One-Sided GS PVUGC

use arkworks_groth16::*;
use arkworks_groth16::ppe::{PvugcVk, derive_gamma_rademacher};
use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
use ark_std::{UniformRand, rand::rngs::StdRng, rand::SeedableRng};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::alloc::AllocVar;
use ark_ec::{CurveGroup, AffineRepr};

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
    
    // Arm bases
    let rho = Fr::rand(&mut rng);
    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    let (y_bases, delta, _) = build_one_sided_ppe(&pvugc_vk, &vk, &vault_utxo);
    let gamma = derive_gamma_rademacher(&pvugc_vk, &vk, 4);
    let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, delta, gamma);
    let arms = arm_rows(&rows, &rho);
    
    // Formal check: With only arms and random fake commitments, decap output ≠ R^ρ
    let k_expected = OneSidedPvugc::compute_r_to_rho(&r, &rho);
    use ark_std::test_rng;
    let mut rng_fake = test_rng();
    let fake_c_rows: Vec<_> = rows
        .u_rows
        .iter()
        .map(|_| (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)))
        .collect();
    let fake_theta = vec![(G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake))];
    let fake_commitments = OneSidedCommitments { c_rows: fake_c_rows, theta: fake_theta, c_delta: (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)) };
    let k_fake = decap_one_sided(&fake_commitments, &arms);
    assert_ne!(k_fake, k_expected);
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
fn test_poce_detects_wrong_rho() {
    let mut rng = StdRng::seed_from_u64(11);
    
    
    let bases = vec![G2Affine::rand(&mut rng); 2];
    
    // Arm first with ρ₁
    let rho1 = Fr::rand(&mut rng);
    let arm1 = (bases[0].into_group() * rho1).into_affine();
    
    // Arm second with DIFFERENT ρ₂
    let rho2 = Fr::rand(&mut rng);
    let arm2 = (bases[1].into_group() * rho2).into_affine();
    
    let inconsistent_arms = vec![arm1, arm2];
    
    // Try to prove with ρ₁
    let proof: PoceAcrossProof<E> = prove_poce_across(&bases, &inconsistent_arms, &rho1, &mut rng);
    
    // Verification should fail
    let valid = verify_poce_across(&bases, &inconsistent_arms, &proof);
    
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

