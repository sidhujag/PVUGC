use std::time::Instant;

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::UniformRand;

// Use the default outer curve to exercise pairings
type E = ark_bw6_761::BW6_761;

use arkworks_groth16::{arming, decap};

// Build a synthetic decap instance with fixed sizes and random scalars
fn build_instance(
    num_cols: usize,
    num_theta: usize,
    rng: &mut ark_std::rand::rngs::StdRng,
) -> (
    Vec<(
        <E as Pairing>::G1Affine,
        <E as Pairing>::G1Affine,
    )>,
    Vec<(
        <E as Pairing>::G1Affine,
        <E as Pairing>::G1Affine,
    )>,
    (
        <E as Pairing>::G1Affine,
        <E as Pairing>::G1Affine,
    ),
    Vec<<E as Pairing>::G2Affine>,
    <E as Pairing>::G2Affine,
) {
    let mut x_b_cols = Vec::with_capacity(num_cols);
    for _ in 0..num_cols {
        let s0 = <E as Pairing>::ScalarField::rand(rng);
        let s1 = <E as Pairing>::ScalarField::rand(rng);
        let g = <E as Pairing>::G1::generator();
        x_b_cols.push(((g * s0).into_affine(), (g * s1).into_affine()));
    }
    let mut theta = Vec::with_capacity(num_theta);
    for _ in 0..num_theta {
        let t0 = <E as Pairing>::ScalarField::rand(rng);
        let t1 = <E as Pairing>::ScalarField::rand(rng);
        let g = <E as Pairing>::G1::generator();
        theta.push(((g * t0).into_affine(), (g * t1).into_affine()));
    }
    let canceller = {
        let s0 = <E as Pairing>::ScalarField::rand(rng);
        let s1 = <E as Pairing>::ScalarField::rand(rng);
        let g = <E as Pairing>::G1::generator();
        ((g * s0).into_affine(), (g * s1).into_affine())
    };
    let mut y_cols_rho = Vec::with_capacity(num_cols);
    for _ in 0..num_cols {
        let s = <E as Pairing>::ScalarField::rand(rng);
        let h = <E as Pairing>::G2::generator();
        y_cols_rho.push((h * s).into_affine());
    }
    let delta_rho = {
        let s = <E as Pairing>::ScalarField::rand(rng);
        let h = <E as Pairing>::G2::generator();
        (h * s).into_affine()
    };
    (x_b_cols, theta, canceller, y_cols_rho, delta_rho)
}

#[test]
fn tost_constant_shape_decap() {
    // Fixed sizes so the loop shape is constant across runs
    let num_cols = 16; // small to keep CI fast
    let num_theta = 8;

    let mut samples = Vec::with_capacity(16);
    for i in 0..16 {
        let mut rng = ark_std::rand::SeedableRng::seed_from_u64(0xDEAD_BEEF ^ (i as u64));
        let (x_b_cols, theta, canceller, y_cols_rho, delta_rho) =
            build_instance(num_cols, num_theta, &mut rng);

        let commitments = decap::OneSidedCommitments::<E> {
            x_b_cols,
            theta,
            theta_delta_cancel: canceller,
        };
        let col_arms = arming::ColumnArms::<E> {
            y_cols_rho,
            delta_rho,
        };

        let start = Instant::now();
        // Run decap once per sample
        let _ = decap::decap::<E>(&commitments, &col_arms).expect("decap");
        let dur = start.elapsed();
        samples.push(dur);
    }

    // Basic TOST-style gate: ensure timing variance is within a reasonable bound
    let min_ns = samples.iter().map(|d| d.as_nanos()).min().unwrap();
    let max_ns = samples.iter().map(|d| d.as_nanos()).max().unwrap();
    // Ratio bound (tunable): allow up to 2x spread to remain resilient to noisy CI nodes
    assert!(max_ns <= min_ns * 2, "timing spread too large: min={}ns max={}ns", min_ns, max_ns);
}

