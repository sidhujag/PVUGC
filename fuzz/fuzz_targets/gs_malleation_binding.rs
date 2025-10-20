#![no_main]

// Goal: Try structured malleations of GS commitments and ensure the full verifier rejects.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr, G1Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{PrimeField, Field};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;

use arkworks_groth16::api::{OneSidedPvugc, PvugcBundle};
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ppe::{PvugcVk, derive_gamma_rademacher};

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

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N { return None; }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    // Choose x = y^2 with y from bytes
    let mut data = data;
    let yb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let seedb = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let opb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let y = Fr::from_le_bytes_mod_order(&yb);
    let x = y.square();
    let seed = u64::from_le_bytes(seedb);
    let op = opb[0] % 5;

    // Setup pk, vk
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let circuit = SqCircuit { x: Some(x), y: Some(y) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    let gamma = derive_gamma_rademacher::<E>(&pvugc_vk, &vk, 4);

    // Make one valid proof and commitments
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder).unwrap();
    let commitments = recorder.build_commitments(&pvugc_vk, &gamma);

    // Baseline must verify true
    let bundle = PvugcBundle { groth16_proof: proof, dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng), dlrep_tie: recorder.create_dlrep_tie(&gamma, &mut rng), gs_commitments: commitments.clone() };
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &[x], &gamma));

    // Apply a single malleation
    let mut mal = commitments.clone();
    match op {
        0 => { // swap two row commitments if possible
            if mal.c_rows.len() >= 2 {
                let i = (seed as usize) % mal.c_rows.len();
                let j = (seed as usize / 3) % mal.c_rows.len();
                mal.c_rows.swap(i, j);
            } else { return; }
        }
        1 => { // swap limbs in one row
            if !mal.c_rows.is_empty() {
                let i = (seed as usize) % mal.c_rows.len();
                let (a, b) = mal.c_rows[i];
                mal.c_rows[i] = (b, a);
            } else { return; }
        }
        2 => { // zero out one theta limb
            if !mal.theta.is_empty() {
                mal.theta[0].0 = G1Affine::identity();
            } else { return; }
        }
        3 => { // perturb first theta limb
            if !mal.theta.is_empty() { mal.theta[0].0 = G1Affine::identity(); } else { return; }
        }
        _ => { // add generator to one limb
            if !mal.c_rows.is_empty() {
                let i = (seed as usize) % mal.c_rows.len();
                let (a, b) = mal.c_rows[i];
                let a2 = (a.into_group() + <E as Pairing>::G1::generator()).into_affine();
                mal.c_rows[i] = (a2, b);
            } else { return; }
        }
    }

    // Reuse same proofs (dlrep proofs bind to original structure). Verifier should reject.
    let bundle_bad = PvugcBundle { groth16_proof: bundle.groth16_proof, dlrep_b: bundle.dlrep_b, dlrep_tie: bundle.dlrep_tie, gs_commitments: mal };
    if OneSidedPvugc::verify(&bundle_bad, &pvugc_vk, &vk, &[x], &gamma) {
        panic!("Malleation accepted by verifier");
    }
});


