#![no_main]

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::PrimeField;

use arkworks_groth16::decap::{decap_one_sided, OneSidedCommitments};
use arkworks_groth16::arming::Arms;

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
    let m = if let Some([b]) = take_bytes::<1>(&mut data) { (b as usize % 6) + 1 } else { return; };
    let t = if let Some([b]) = take_bytes::<1>(&mut data) { (b as usize % 4) + 1 } else { return; };

    // Build commitments.c_rows of length m
    let mut c_rows = Vec::with_capacity(m);
    for _ in 0..m {
        let s0 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let s1 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let p0 = (<E as Pairing>::G1::generator() * s0).into_affine();
        let p1 = (<E as Pairing>::G1::generator() * s1).into_affine();
        c_rows.push((p0, p1));
    }

    // Theta of length t
    let mut theta = Vec::with_capacity(t);
    for _ in 0..t {
        let s0 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let s1 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let p0 = (<E as Pairing>::G1::generator() * s0).into_affine();
        let p1 = (<E as Pairing>::G1::generator() * s1).into_affine();
        theta.push((p0, p1));
    }

    let commitments = OneSidedCommitments { c_rows, theta };

    // Arms: u_rows_rho length m; single w_rows_rho
    let mut u_rows_rho = Vec::with_capacity(m);
    for _ in 0..m {
        let s = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        u_rows_rho.push((<E as Pairing>::G2::generator() * s).into_affine());
    }
    let sw = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
    let w_rows_rho = vec![(<E as Pairing>::G2::generator() * sw).into_affine()];
    let arms = Arms { u_rows_rho, w_rows_rho };

    let _ = decap_one_sided::<E>(&commitments, &arms);
});


