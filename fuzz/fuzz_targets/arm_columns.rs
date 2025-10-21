#![no_main]

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::{PrimeField, Zero};

use arkworks_groth16::arming::{arm_columns, ColumnBases};

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

    // Build y_cols as multiples of generator
    let mut y_cols = Vec::with_capacity(m);
    for _ in 0..m {
        let bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
        let s = Fr::from_le_bytes_mod_order(&bytes);
        let p = (<E as Pairing>::G2::generator() * s).into_affine();
        y_cols.push(p);
    }

    // Build delta
    let bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
    let s = Fr::from_le_bytes_mod_order(&bytes);
    let delta = (<E as Pairing>::G2::generator() * s).into_affine();

    let cols: ColumnBases<E> = ColumnBases { y_cols, delta };

    // rho
    let rho_bytes = if let Some(arr) = take_bytes::<32>(&mut data) { arr } else { return; };
    let rho = Fr::from_le_bytes_mod_order(&rho_bytes);
    
    // Skip zero rho to avoid panic
    if rho.is_zero() { return; }

    let _arms = arm_columns::<E>(&cols, &rho);
});


