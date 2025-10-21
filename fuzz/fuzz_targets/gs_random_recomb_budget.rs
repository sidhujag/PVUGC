#![no_main]

// Goal: Random linear recombination of multiple GS rows under a small budget and attempt
// naive reproof; verification must fail.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_std::Zero;
use ark_ff::{PrimeField, Field};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;

use arkworks_groth16::api::{OneSidedPvugc, PvugcBundle};
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ppe::PvugcVk;

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

fn small(b: u8) -> i64 { (b % 7) as i64 - 3 }

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    let yb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let seedb = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let budgetb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let y = Fr::from_le_bytes_mod_order(&yb);
    let x = y.square();
    let seed = u64::from_le_bytes(seedb);
    let budget = (budgetb[0] as usize % 5) + 1; // combine up to 1..=5 rows

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let circuit = SqCircuit { x: Some(x), y: Some(y) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };

    let mut rec = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut rec).unwrap();
    let mut commitments = rec.build_commitments();
    let dlrep_b = rec.create_dlrep_b(&pvugc_vk, &mut rng);
    let dlrep_tie = rec.create_dlrep_tie(&mut rng);

    let base_bundle = PvugcBundle { groth16_proof: proof, dlrep_b, dlrep_tie, gs_commitments: commitments.clone() };
    assert!(OneSidedPvugc::verify(&base_bundle, &pvugc_vk, &vk, &[x]));

    if commitments.x_b_cols.is_empty() { return; }

    // Randomly pick up to `budget` rows, recombine with small coefficients into row 0
    use ark_ec::CurveGroup;
    let n = commitments.x_b_cols.len();
    let k = budget.min(n);
    let mut acc0 = <E as Pairing>::G1::zero();
    let mut acc1 = <E as Pairing>::G1::zero();
    for i in 0..k {
        let coeff = small(take_bytes::<1>(&mut data).unwrap_or([1])[0]);
        if coeff == 0 { continue; }
        let (a, b) = commitments.x_b_cols[i];
        acc0 += a.into_group() * Fr::from(coeff);
        acc1 += b.into_group() * Fr::from(coeff);
    }
    commitments.x_b_cols[0] = (acc0.into_affine(), acc1.into_affine());

    // Keep DLREP proofs unchanged; verifier should reject
    let bundle_bad = PvugcBundle { groth16_proof: base_bundle.groth16_proof, dlrep_b: base_bundle.dlrep_b, dlrep_tie: base_bundle.dlrep_tie, gs_commitments: commitments };
    if OneSidedPvugc::verify(&bundle_bad, &pvugc_vk, &vk, &[x]) {
        panic!("Random recombination accepted");
    }
});


