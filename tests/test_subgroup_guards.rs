use ark_bls12_381::{Bls12_381 as E, Fr, G1Affine, G2Affine};
use ark_std::UniformRand;
use ark_std::rand::SeedableRng;
use ark_groth16::Groth16;
use ark_snark::SNARK;

use arkworks_groth16::ppe::validate_groth16_vk_subgroups;
use arkworks_groth16::arming::{RowBases, arm_rows};

#[test]
fn reject_zero_points_in_vk() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    #[derive(Clone)] struct C { }
    impl ConstraintSynthesizer<Fr> for C {
        fn generate_constraints(self, _cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> { Ok(()) }
    }
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0);
    let (_pk, mut vk) = Groth16::<E>::circuit_specific_setup(C{}, &mut rng).unwrap();
    // Force zero
    vk.alpha_g1 = G1Affine::identity();
    assert!(!validate_groth16_vk_subgroups(&vk));
}

#[test]
fn arm_rows_allows_some_identity_rows_but_not_all() {
    // one identity and one non-identity row per side
    let mut rng = ark_std::test_rng();
    let rows = RowBases::<E> {
        u_rows: vec![G2Affine::identity(), G2Affine::rand(&mut rng)],
        w_rows: vec![G2Affine::identity(), G2Affine::rand(&mut rng)],
        gamma: vec![], // as needed
    };
    let rho = Fr::from(1u64);
    let arms = arm_rows(&rows, &rho);
    assert_eq!(arms.u_rows_rho.len(), 2);
    assert_eq!(arms.w_rows_rho.len(), 2);
}

#[test]
#[should_panic]
fn arm_rows_rejects_all_identity_side() {
    // All U rows identity → reject
    let rows = RowBases::<E> { u_rows: vec![G2Affine::identity()], w_rows: vec![G2Affine::rand(&mut ark_std::test_rng())], gamma: vec![vec![]] };
    let rho = Fr::from(1u64);
    let _ = arm_rows(&rows, &rho);
}

