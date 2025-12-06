#![no_main]

// Goal: try to find two different statements (public inputs) that decapsulate to the same K
// for the same rho, which should not happen: K = R(vk, x)^rho must differ if x differs.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ff::{Field, PrimeField, Zero};
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_snark::SNARK;
use once_cell::sync::Lazy;
use std::sync::Mutex;
use ark_std::rand::SeedableRng;

use arkworks_groth16::api::OneSidedPvugc;
use arkworks_groth16::ppe::{PvugcVk, compute_groth16_target};
use arkworks_groth16::decap::{OneSidedCommitments, prove_and_build_commitments};

// Simple y^2 = x circuit: public x, witness y
#[derive(Clone)]
struct SqCircuit { pub x: Option<Fr>, pub y: Option<Fr> }

impl ConstraintSynthesizer<Fr> for SqCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::eq::EqGadget;
        let x = ark_r1cs_std::fields::fp::FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y = ark_r1cs_std::fields::fp::FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y2 = &y * &y;
        x.enforce_equal(&y2)?;
        Ok(())
    }
}

static SETUP: Lazy<Mutex<(ProvingKey<E>, VerifyingKey<E>)>> = Lazy::new(|| {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0);
    let circuit = SqCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (pk, vk) = Groth16::<E, ark_groth16::r1cs_to_qap::PvugcReduction>::circuit_specific_setup(circuit, &mut rng).unwrap();
    Mutex::new((pk, vk))
});

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N { return None; }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    // Two witnesses y1, y2 → public inputs x1=y1^2, x2=y2^2, and a rho
    let b1 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let b2 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let b3 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let y1 = Fr::from_le_bytes_mod_order(&b1);
    let y2 = Fr::from_le_bytes_mod_order(&b2);
    let x1 = y1.square();
    let x2 = y2.square();
    let rho = Fr::from_le_bytes_mod_order(&b3);
    
    // Skip zero rho to avoid panic
    if rho.is_zero() { return; }

    // Avoid trivial equal statements
    if x1 == x2 { return; }

    let (pk, vk) = {
        let g = SETUP.lock().unwrap();
        (g.0.clone(), g.1.clone())
    };

    // Construct pvugc-vk wrapper from pk and vk
    // t_const_points_gt must have length = gamma_abc_g1.len()
    use ark_ff::Field;
    let t_dummy = vec![
        ark_ec::pairing::PairingOutput(<<E as ark_ec::pairing::Pairing>::TargetField as Field>::ONE);
        vk.gamma_abc_g1.len()
    ];
    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        vk.beta_g2,
        vk.delta_g2,
        pk.b_g2_query.clone(),
        t_dummy,
    );


    // Canonical column setup for statement 1
    let statement1 = vec![x1];
    let statement2 = vec![x2];
    let (_bases_cols, col_arms, _r, _k) =
        OneSidedPvugc::setup_and_arm::<E>(&pvugc_vk, &vk, &statement1, &rho).expect("setup_and_arm");
    let r1 = compute_groth16_target::<E>(&vk, &statement1).expect("compute_groth16_target");
    let r2 = compute_groth16_target::<E>(&vk, &statement2).expect("compute_groth16_target");

    // Take k1 = r1^rho and k2 = r2^rho; then assert k1 != k2 for x1 != x2.
    let k1 = OneSidedPvugc::compute_r_to_rho::<E>(&r1, &rho);
    let k2 = OneSidedPvugc::compute_r_to_rho::<E>(&r2, &rho);

    if k1 == k2 {
        panic!("Found K collision across different statements");
    }

    // Optionally exercise decap with real commitments: build two proofs and ensure mismatch
    // (kept lightweight: skip if data too short)
    if let (Some(s1b), Some(s2b)) = (take_bytes::<8>(&mut data), take_bytes::<8>(&mut data)) {
        let mut rng1 = ark_std::rand::rngs::StdRng::seed_from_u64(u64::from_le_bytes(s1b));
        let mut rng2 = ark_std::rand::rngs::StdRng::seed_from_u64(u64::from_le_bytes(s2b));
        
        // Proof 1 for x1
        let (proof1, commitments1, _assignment1, _s1) = 
            prove_and_build_commitments(&pk, SqCircuit { x: Some(x1), y: Some(y1) }, &mut rng1).unwrap();
        let kd1 = OneSidedPvugc::decapsulate::<E>(&commitments1, &col_arms).expect("decapsulate");
        if kd1 != k1 {
            panic!("Decap mismatch for statement 1");
        }
        
        // Setup and proof for statement 2 with its own arms
        let (_bases_cols2, col_arms2, _r2, _k2_setup) =
            OneSidedPvugc::setup_and_arm::<E>(&pvugc_vk, &vk, &statement2, &rho)
                .expect("setup_and_arm for stmt2");
        
        let (proof2, commitments2, _assignment2, _s2) = 
            prove_and_build_commitments(&pk, SqCircuit { x: Some(x2), y: Some(y2) }, &mut rng2).unwrap();
        let kd2 = OneSidedPvugc::decapsulate::<E>(&commitments2, &col_arms2).expect("decapsulate");
        if kd2 != k2 {
            panic!("Decap mismatch for statement 2");
        }
        if kd1 == kd2 {
            panic!("Decap collision across different statements");
        }
        let _ = (proof1, proof2);
    }
});
