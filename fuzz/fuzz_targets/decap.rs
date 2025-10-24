#![no_main]

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup, AffineRepr};
use ark_ff::{PrimeField, Zero, Field};

use arkworks_groth16::decap::{OneSidedCommitments, decap};
use arkworks_groth16::arming::{ColumnArms};

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
    let rhobytes = if let Some(b) = take_bytes::<32>(&mut data) { b } else { return; };
    let rho = Fr::from_le_bytes_mod_order(&rhobytes);
    if rho.is_zero() { return; }

    // Build commitments.x_b_cols of length m
    let mut x_b_cols = Vec::with_capacity(m);
    for _ in 0..m {
        let s0 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let s1 = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        let p0 = (<E as Pairing>::G1::generator() * s0).into_affine();
        let p1 = (<E as Pairing>::G1::generator() * s1).into_affine();
        x_b_cols.push((p0, p1));
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

    // Require canceller limbs
    let c0 = (<E as Pairing>::G1::generator() * Fr::from(1u64)).into_affine();
    let c1 = (<E as Pairing>::G1::generator() * Fr::from(0u64)).into_affine();
    let commitments = OneSidedCommitments { x_b_cols, theta, theta_delta_cancel: (c0, c1) };

    // Build base columns and compute arms as rho-powers of those bases
    let mut y_cols = Vec::with_capacity(m);
    for _ in 0..m {
        let s = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
        y_cols.push((<E as Pairing>::G2::generator() * s).into_affine());
    }
    let sd = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([0u8; 32]));
    let delta = (<E as Pairing>::G2::generator() * sd).into_affine();
    let y_cols_rho: Vec<_> = y_cols.iter().map(|y| (y.into_group() * rho).into_affine()).collect();
    let delta_rho = (delta.into_group() * rho).into_affine();
    let col_arms = ColumnArms { y_cols_rho, delta_rho };

    // Unarmed PPE (R) from synthetic bases
    use ark_ec::pairing::PairingOutput;
    use ark_std::One;
    let mut r = PairingOutput::<E>(One::one());
    for ((x0, x1), y) in commitments.x_b_cols.iter().zip(&y_cols) {
        r += E::pairing(*x0, *y);
        r += E::pairing(*x1, *y);
    }
    for (t0, t1) in &commitments.theta {
        r += E::pairing(*t0, delta);
        r += E::pairing(*t1, delta);
    }
    let (cc0, cc1) = commitments.theta_delta_cancel;
    r += E::pairing(cc0, delta);
    r += E::pairing(cc1, delta);

    // Expected K = R^rho
    let k_expected = PairingOutput::<E>(r.0.pow(rho.into_bigint()));
    let k_actual = decap::<E>(&commitments, &col_arms).expect("decap");
    if !arkworks_groth16::ct::gt_eq_ct::<E>(&k_actual, &k_expected) {
        panic!("Decap fuzzer equality failed: K != R^rho");
    }
});


