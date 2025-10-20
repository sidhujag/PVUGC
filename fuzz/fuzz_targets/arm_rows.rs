#![no_main]

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::{PrimeField, Zero};

use arkworks_groth16::arming::{arm_rows, RowBases};

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N { return None; }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    // Sizes
    let mut data = data;
    let m = if let Some([b]) = take_bytes::<1>(&mut data) { (b as usize % 6) + 1 } else { return; };

    // Build u_rows and w_rows as multiples of generator
    let mut u_rows = Vec::with_capacity(m);
    for _ in 0..m {
        let bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
        let s = Fr::from_le_bytes_mod_order(&bytes);
        let p = (<E as Pairing>::G2::generator() * s).into_affine();
        u_rows.push(p);
    }

    let bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
    let s = Fr::from_le_bytes_mod_order(&bytes);
    let w = (<E as Pairing>::G2::generator() * s).into_affine();
    let w_rows = vec![w];

    // Gamma is not used by arm_rows but RowBases requires it
    let gamma = vec![vec![Fr::from(1u64)]];

    let rows: RowBases<E> = RowBases { u_rows, w_rows, gamma };

    // rho
    let rho_bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
    let rho = Fr::from_le_bytes_mod_order(&rho_bytes);
    
    // Skip zero rho to avoid panic
    if rho.is_zero() { return; }

    let _arms = arm_rows::<E>(&rows, &rho);
});


