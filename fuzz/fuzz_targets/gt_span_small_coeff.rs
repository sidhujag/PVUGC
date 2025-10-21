#![no_main]

// Goal: Try to witness a small-coefficient GT-span relation for R(vk,x):
// find small integers a0,a1 and c_ell,d such that e(a0*alpha_g1 + a1*gamma_abc_g1[0], sum c_ell*U_ell + d*delta) == R.
// If found, panic (indicates potential grindable bad instance).

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_std::{Zero, rand::SeedableRng};
use ark_ff::PrimeField;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;

use arkworks_groth16::arming::ColumnBases;
use arkworks_groth16::ppe::{PvugcVk, build_one_sided_ppe, compute_groth16_target};

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

fn map_small(b: u8, bound: i32) -> i32 {
    // map byte to [-bound, bound]
    let span = (2*bound + 1) as u8;
    (i32::from(b % span)) - bound
}

fuzz_target!(|data: &[u8]| {
    // x, seeds, search parameters
    let mut data = data;
    let xb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let seedb = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let sb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let samplesb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let x = Fr::from_le_bytes_mod_order(&xb);
    let seed = u64::from_le_bytes(seedb);
    let bound = ((sb[0] % 3) + 1) as i32; // 1..=3
    let samples = (samplesb[0] as usize % 60) + 20; // 20..=79 samples

    // Setup a tiny circuit VK deterministically from seed
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let circuit = SqCircuit { x: Some(x), y: None };
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();

    // Build PVUGC VK using vk and pk-like fields where needed; here only vk is used
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: vec![] };

    // Derive column bases from VK Y-bases: {β} ∪ b_g2_query; if query empty, we still have β
    // Extract Y from pvugc_vk via build_one_sided_ppe path
    let (y_bases, delta, _r_target) = build_one_sided_ppe::<E>(&pvugc_vk, &vk, &[x]);
    let cols: ColumnBases<E> = ColumnBases { y_cols: y_bases, delta };
    let y_cols: Vec<G2Affine> = cols.y_cols;
    let delta_g2: G2Affine = cols.delta;

    // Target R(vk, x)
    let r = compute_groth16_target::<E>(&vk, &[x]);

    // G1 basis: pick two from VK
    let b0 = vk.alpha_g1.into_group();
    let b1 = vk.gamma_abc_g1[0].into_group();

    // Randomly sample small coefficient combinations
    for _ in 0..samples {
        let ab = if let Some([a]) = take_bytes::<1>(&mut data) { a } else { break; };
        let bb = if let Some([b]) = take_bytes::<1>(&mut data) { b } else { break; };
        let c0b = if let Some([c]) = take_bytes::<1>(&mut data) { c } else { break; };
        let c1b = if let Some([c]) = take_bytes::<1>(&mut data) { c } else { break; };
        let db = if let Some([d]) = take_bytes::<1>(&mut data) { d } else { break; };

        let a0 = map_small(ab, bound);
        let a1 = map_small(bb, bound);
        let c0 = map_small(c0b, bound);
        let c1 = map_small(c1b, bound);
        let d = map_small(db, bound);

        // Build A* in G1
        let mut a_star = <E as Pairing>::G1::zero();
        if a0 != 0 { a_star += b0 * Fr::from(a0 as i64); }
        if a1 != 0 { a_star += b1 * Fr::from(a1 as i64); }
        let a_star = a_star.into_affine();

        // Build Q* in G2 using first up to two Y columns
        let mut q_star = <E as Pairing>::G2::zero();
        if !y_cols.is_empty() && c0 != 0 { q_star += y_cols[0].into_group() * Fr::from(c0 as i64); }
        if y_cols.len() > 1 && c1 != 0 { q_star += y_cols[1].into_group() * Fr::from(c1 as i64); }
        if d != 0 { q_star += delta_g2.into_group() * Fr::from(d as i64); }
        let q_star = q_star.into_affine();

        if <E as Pairing>::pairing(a_star, q_star) == r {
            panic!("GT small-coeff span witness found");
        }
    }
});


