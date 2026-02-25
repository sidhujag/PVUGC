//! Regression tests for BW6-761 "same math" optimizations used in the SP1 guest.
//!
//! Goal: ensure the custom windowed routines are EXACTLY equivalent to arkworks reference ops.

use ark_bw6_761::BW6_761;
use ark_ec::{pairing::Pairing, AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, CyclotomicMultSubgroup, One, PrimeField, UniformRand, Zero};
use ark_std::rand::{rngs::StdRng, SeedableRng};

fn cyclotomic_exp_windowed(
    base: &<BW6_761 as Pairing>::TargetField,
    exp: <<BW6_761 as Pairing>::ScalarField as PrimeField>::BigInt,
) -> <BW6_761 as Pairing>::TargetField {
    const W: usize = 5;
    if exp.is_zero() {
        return <BW6_761 as Pairing>::TargetField::one();
    }

    let g = base.clone();
    let g2 = g.cyclotomic_square();
    let mut table = Vec::with_capacity(1 << (W - 1));
    table.push(g.clone());
    for i in 1..(1 << (W - 1)) {
        let mut next = table[i - 1].clone();
        next *= &g2;
        table.push(next);
    }

    let bits_le = exp.to_bits_le();
    let mut i: isize = (bits_le.len() as isize) - 1;
    while i >= 0 && !bits_le[i as usize] {
        i -= 1;
    }
    if i < 0 {
        return <BW6_761 as Pairing>::TargetField::one();
    }

    let mut acc = <BW6_761 as Pairing>::TargetField::one();
    while i >= 0 {
        if !bits_le[i as usize] {
            acc = acc.cyclotomic_square();
            i -= 1;
            continue;
        }

        let max_j = core::cmp::max(0, i as isize - (W as isize) + 1);
        let mut j = max_j;
        while j < i && !bits_le[j as usize] {
            j += 1;
        }

        let mut value: usize = 0;
        for k in (j..=i).rev() {
            value = (value << 1) | (bits_le[k as usize] as usize);
        }
        assert!(value & 1 == 1);
        assert!(value < (1 << W));

        let win_len = (i - j + 1) as usize;
        for _ in 0..win_len {
            acc = acc.cyclotomic_square();
        }
        acc *= &table[value >> 1];
        i = j - 1;
    }

    acc
}

fn g2_mul_windowed(
    base: &<BW6_761 as Pairing>::G2Affine,
    exp: <<BW6_761 as Pairing>::ScalarField as PrimeField>::BigInt,
) -> <BW6_761 as Pairing>::G2 {
    // Must match the deployed guest configuration.
    const W: usize = 5;
    if exp.is_zero() {
        return <BW6_761 as Pairing>::G2::zero();
    }

    let p = base.into_group();
    if p.is_zero() {
        return p;
    }

    let mut p2 = p.clone();
    p2.double_in_place();

    let mut table = Vec::with_capacity(1 << (W - 1));
    table.push(p.clone());
    for i in 1..(1 << (W - 1)) {
        let mut next = table[i - 1].clone();
        next += &p2;
        table.push(next);
    }

    let bits_le = exp.to_bits_le();
    let mut i: isize = (bits_le.len() as isize) - 1;
    while i >= 0 && !bits_le[i as usize] {
        i -= 1;
    }
    if i < 0 {
        return <BW6_761 as Pairing>::G2::zero();
    }

    let mut acc = <BW6_761 as Pairing>::G2::zero();
    while i >= 0 {
        if !bits_le[i as usize] {
            acc.double_in_place();
            i -= 1;
            continue;
        }

        let max_j = core::cmp::max(0, i as isize - (W as isize) + 1);
        let mut j = max_j;
        while j < i && !bits_le[j as usize] {
            j += 1;
        }

        let mut value: usize = 0;
        for k in (j..=i).rev() {
            value = (value << 1) | (bits_le[k as usize] as usize);
        }
        assert!(value & 1 == 1);
        assert!(value < (1 << W));

        let win_len = (i - j + 1) as usize;
        for _ in 0..win_len {
            acc.double_in_place();
        }
        acc += &table[value >> 1];
        i = j - 1;
    }

    acc
}

#[test]
fn bw6_windowed_matches_reference() {
    let mut rng = StdRng::seed_from_u64(20260223);

    // Base GT in cyclotomic subgroup (pairing output).
    let gt_base = <BW6_761 as Pairing>::pairing(
        <BW6_761 as Pairing>::G1::generator(),
        <BW6_761 as Pairing>::G2::generator(),
    )
    .0;

    // Edge scalars + randoms.
    let mut scalars = vec![
        <BW6_761 as Pairing>::ScalarField::zero(),
        <BW6_761 as Pairing>::ScalarField::one(),
        -<BW6_761 as Pairing>::ScalarField::one(),
        <BW6_761 as Pairing>::ScalarField::from(2u64),
        <BW6_761 as Pairing>::ScalarField::from(3u64),
    ];
    for _ in 0..50 {
        scalars.push(<BW6_761 as Pairing>::ScalarField::rand(&mut rng));
    }

    for rho in scalars {
        let rho_big = rho.into_bigint();

        // GT exponentiation equivalence.
        let ref_gt = gt_base.cyclotomic_exp(rho_big);
        let win_gt = cyclotomic_exp_windowed(&gt_base, rho_big);
        assert_eq!(ref_gt, win_gt, "cyclotomic exp mismatch");

        // G2 scalar mul equivalence.
        let g2 = (<BW6_761 as Pairing>::G2::generator() * <BW6_761 as Pairing>::ScalarField::rand(&mut rng)).into_affine();
        let ref_g2 = g2.mul_bigint(rho_big);
        let win_g2 = g2_mul_windowed(&g2, rho_big);
        assert_eq!(ref_g2, win_g2, "G2 mul mismatch");
    }
}

