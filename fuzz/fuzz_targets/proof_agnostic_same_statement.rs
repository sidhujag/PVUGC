#![no_main]

// Goal: For the SAME statement (vk, x) and SAME ρ, two DIFFERENT valid proofs
// must decapsulate to the SAME key K = R(vk, x)^ρ (proof-agnostic property).

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ff::{Field, PrimeField, Zero};
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use once_cell::sync::Lazy;
use std::sync::Mutex;
use ark_std::rand::SeedableRng;

use arkworks_groth16::api::OneSidedPvugc;
use arkworks_groth16::ppe::{PvugcVk};

// Circuit: enforce x = y^2
#[derive(Clone)]
struct SqCircuit { pub x: Option<Fr>, pub y: Option<Fr> }

impl ConstraintSynthesizer<Fr> for SqCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::eq::EqGadget;
        let x = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y2 = &y * &y;
        x.enforce_equal(&y2)?;
        Ok(())
    }
}

static SETUP: Lazy<Mutex<(ProvingKey<E>, VerifyingKey<E>)>> = Lazy::new(|| {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(1);
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
    // Choose y from bytes; compute x = y^2 to make a valid statement
    let mut data = data;
    let yb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let rhob = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let seed1b = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let seed2b = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let y = Fr::from_le_bytes_mod_order(&yb);
    let x = y.square();
    let rho = Fr::from_le_bytes_mod_order(&rhob);
    
    // Skip zero rho to avoid panic
    if rho.is_zero() { return; }
    let seed1 = u64::from_le_bytes(seed1b);
    let seed2 = u64::from_le_bytes(seed2b);

    let (pk, vk) = {
        let g = SETUP.lock().unwrap();
        (g.0.clone(), g.1.clone())
    };

    // Statement-only PVUGC VK
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()) };

    // Canonical column setup and arming
    let (_bases, col_arms, _r, k_expected_from_setup) = OneSidedPvugc::setup_and_arm::<E>(&pvugc_vk, &vk, &[x], &rho);

    // Deterministic RNGs
    let mut rng1 = ark_std::rand::rngs::StdRng::seed_from_u64(seed1);
    let mut rng2 = ark_std::rand::rngs::StdRng::seed_from_u64(seed2 ^ 0x9e3779b97f4a7c15);

    // Build two independent proofs with hook to record coefficients
    let mut rec1 = arkworks_groth16::coeff_recorder::SimpleCoeffRecorder::<E>::new();
    let _proof1 = Groth16::<E>::create_random_proof_with_hook(
        SqCircuit { x: Some(x), y: Some(y) },
        &pk,
        &mut rng1,
        &mut rec1,
    ).unwrap();
    let commitments1: arkworks_groth16::decap::OneSidedCommitments<E> = rec1.build_commitments();

    let mut rec2 = arkworks_groth16::coeff_recorder::SimpleCoeffRecorder::<E>::new();
    let _proof2 = Groth16::<E>::create_random_proof_with_hook(
        SqCircuit { x: Some(x), y: Some(y) },
        &pk,
        &mut rng2,
        &mut rec2,
    ).unwrap();
    let commitments2: arkworks_groth16::decap::OneSidedCommitments<E> = rec2.build_commitments();

    // Decap both; they must be identical and equal R^ρ
    let k1 = OneSidedPvugc::decapsulate::<E>(&commitments1, &col_arms);
    let k2 = OneSidedPvugc::decapsulate::<E>(&commitments2, &col_arms);
    if k1 != k2 {
        panic!("Proof-agnostic violation: K1 != K2 for same (vk,x,rho)");
    }

    // Check against target r^rho
    if k1 != k_expected_from_setup {
        panic!("Decap mismatch: K != R^rho for same statement");
    }
});


