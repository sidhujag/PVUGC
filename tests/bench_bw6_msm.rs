use ark_bw6_761::{Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::UniformRand;
use std::time::Instant;

#[test]
fn bench_bw6_msm_small() {
    let mut rng = ark_std::test_rng();
    let size = 10;
    let count = 1000;
    
    let bases: Vec<G1Affine> = (0..size).map(|_| G1Projective::rand(&mut rng).into_affine()).collect();
    let scalars: Vec<Fr> = (0..size).map(|_| Fr::rand(&mut rng)).collect();

    let start = Instant::now();
    for _ in 0..count {
        let _ = G1Projective::msm(&bases, &scalars).unwrap();
    }
    let elapsed = start.elapsed();
    println!("Average MSM (size={}): {:?}", size, elapsed / count as u32);
}

