#![no_main]

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr, G2Affine};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::PrimeField;

use arkworks_groth16::arming::build_row_bases_from_vk;

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N { return None; }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    // Dimensions
    let mut data = data;
    let rows = if let Some([b]) = take_bytes::<1>(&mut data) { (b as usize % 6) + 1 } else { return; };
    let cols = if let Some([b]) = take_bytes::<1>(&mut data) { (b as usize % 6) + 1 } else { return; };

    // y_bases (cols)
    let mut y_bases: Vec<G2Affine> = Vec::with_capacity(cols);
    for _ in 0..cols {
        let sb = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
        let s = Fr::from_le_bytes_mod_order(&sb);
        y_bases.push((<E as Pairing>::G2::generator() * s).into_affine());
    }

    // delta
    let db = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
    let d = Fr::from_le_bytes_mod_order(&db);
    let delta = (<E as Pairing>::G2::generator() * d).into_affine();

    // gamma rows x cols
    let mut gamma: Vec<Vec<Fr>> = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            let gb = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
            row.push(Fr::from_le_bytes_mod_order(&gb));
        }
        gamma.push(row);
    }

    let _ = build_row_bases_from_vk::<E>(&y_bases, delta, gamma);
});


