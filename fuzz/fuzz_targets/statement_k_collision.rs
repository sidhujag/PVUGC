#![no_main]

// Goal: try to find two different statements (public inputs) that decapsulate to the same K
// for the same rho, which should not happen: K = R(vk, x)^rho must differ if x differs.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::pairing::PairingOutput;
use ark_ff::{Field, PrimeField, Zero};
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_snark::SNARK;
use once_cell::sync::Lazy;
use std::sync::Mutex;
use ark_std::rand::SeedableRng;

use arkworks_groth16::arming::{arm_rows, build_row_bases_from_vk, Arms};
use arkworks_groth16::ppe::{PvugcVk, build_one_sided_ppe, compute_groth16_target, derive_gamma_rademacher};
use arkworks_groth16::decap::{OneSidedCommitments, decap_one_sided};

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
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
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
    // Two public inputs x1, x2 as field elements, and a rho
    let b1 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let b2 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let b3 = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let x1 = Fr::from_le_bytes_mod_order(&b1);
    let x2 = Fr::from_le_bytes_mod_order(&b2);
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
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };

    // Deterministic thin gamma
    let gamma = derive_gamma_rademacher::<E>(&pvugc_vk, &vk, 4);

    // Build Y, delta, target for each statement and rows/arms once per statement
    let (y_bases, delta, _r1) = build_one_sided_ppe::<E>(&pvugc_vk, &vk, &[x1]);
    let rows1 = build_row_bases_from_vk::<E>(&y_bases, delta, gamma.clone());
    let arms1: Arms<E> = arm_rows::<E>(&rows1, &rho);
    let r1 = compute_groth16_target::<E>(&vk, &[x1]);

    let (_, _, _r2) = build_one_sided_ppe::<E>(&pvugc_vk, &vk, &[x2]);
    let rows2 = build_row_bases_from_vk::<E>(&y_bases, delta, gamma.clone());
    let arms2: Arms<E> = arm_rows::<E>(&rows2, &rho);
    let r2 = compute_groth16_target::<E>(&vk, &[x2]);

    // Take k1 = r1^rho and k2 = r2^rho; then assert k1 != k2 for x1 != x2.
    let k1 = PairingOutput::<E>(r1.0.pow(rho.into_bigint()));
    let k2 = PairingOutput::<E>(r2.0.pow(rho.into_bigint()));

    if k1 == k2 {
        panic!("Found K collision across different statements");
    }

    // Still exercise decap path structurally with arbitrary commitments to avoid dead code: use zero-length
    let commitments = OneSidedCommitments::<E> { c_rows: vec![], theta: vec![] };
    let _ = decap_one_sided::<E>(&commitments, &arms1);
    let _ = decap_one_sided::<E>(&commitments, &arms2);
});


