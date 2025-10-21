use ark_bls12_381::{Bls12_381 as E, Fr, G1Affine, G2Affine};
use ark_std::UniformRand;
use ark_std::rand::SeedableRng;
use ark_groth16::Groth16;
use ark_snark::SNARK;

use arkworks_groth16::ppe::validate_groth16_vk_subgroups;
use arkworks_groth16::arming::{ColumnBases, arm_columns};

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
fn arm_columns_allows_some_identity_cols_but_not_all() {
    // one identity and one non-identity column per side
    let mut rng = ark_std::test_rng();
    let cols = ColumnBases::<E> {
        y_cols: vec![G2Affine::identity(), G2Affine::rand(&mut rng)],
        delta: G2Affine::rand(&mut rng),
    };
    let rho = Fr::from(1u64);
    let arms = arm_columns(&cols, &rho);
    assert_eq!(arms.y_cols_rho.len(), 2);
}

#[test]
#[should_panic]
fn arm_columns_rejects_zero_delta() {
    // Zero delta → reject
    let cols = ColumnBases::<E> { 
        y_cols: vec![G2Affine::rand(&mut ark_std::test_rng())], 
        delta: G2Affine::identity() 
    };
    let rho = Fr::from(1u64);
    let _ = arm_columns(&cols, &rho);
}

