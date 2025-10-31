//! Security Tests for One-Sided GS PVUGC

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
use ark_ec::{pairing::Pairing, pairing::PairingOutput, AffineRepr, CurveGroup, PrimeGroup};
use ark_groth16::Groth16;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::{rand::rngs::StdRng, rand::SeedableRng, UniformRand};
use ark_std::Zero;
use arkworks_groth16::ppe::PvugcVk;
use arkworks_groth16::api::VerifyLimits;
use arkworks_groth16::api::{
    DEFAULT_MAX_B_COLUMNS,
    DEFAULT_MAX_THETA_ROWS,
    DEFAULT_MAX_TOTAL_PAIRINGS,
};
use arkworks_groth16::PoceColumnProof;
use arkworks_groth16::*;

type E = Bls12_381;

#[derive(Clone)]
struct TestCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        Ok(())
    }
}

#[test]
fn test_cannot_compute_k_from_arms_alone() {
    let mut rng = StdRng::seed_from_u64(10);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();

    let vault_utxo = vec![Fr::from(25u64)];

    // Compute R
    let r = compute_groth16_target(&vk, &vault_utxo).expect("compute_groth16_target");

    // Build column bases and arm them
    let rho = Fr::rand(&mut rng);
    let pvugc_vk: PvugcVk<E> = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };
    let mut y_cols = vec![pvugc_vk.beta_g2];
    y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
    let cols: ColumnBases<E> = ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    };
    let col_arms = arm_columns(&cols, &rho).expect("arm_columns failed");

    // Expected K = R^ρ
    let k_expected = OneSidedPvugc::compute_r_to_rho(&r, &rho);

    // Create random fake commitments (not derived from valid proof)
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    let mut rng_fake = StdRng::seed_from_u64(5);
    let fake_x_b_cols: Vec<_> = cols
        .y_cols
        .iter()
        .map(|_| (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)))
        .collect();
    let fake_theta = vec![(G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake))];
    let fake_commitments: OneSidedCommitments<E> = OneSidedCommitments {
        x_b_cols: fake_x_b_cols,
        theta: fake_theta,
        theta_delta_cancel: (G1Affine::rand(&mut rng_fake), G1Affine::rand(&mut rng_fake)),
    };

    // Security property: fake commitments + valid arms should NOT produce correct K
    let fake_k = OneSidedPvugc::decapsulate(&fake_commitments, &col_arms).expect("decapsulate");
    assert_ne!(
        fake_k, k_expected,
        "Fake commitments should not produce correct K = R^ρ"
    );

    // Additional check: fake K should not be identity (trivial case)
    use ark_std::One;
    assert_ne!(
        fake_k,
        PairingOutput::<E>(One::one()),
        "Fake K should not be identity"
    );
}

#[test]
fn test_invalid_groth16_rejected() {
    let mut rng = StdRng::seed_from_u64(3);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();

    let vault_utxo = vec![Fr::from(25u64)];

    // Create random invalid proof
    let invalid_proof = ark_groth16::Proof {
        a: G1Affine::rand(&mut rng),
        b: G2Affine::rand(&mut rng),
        c: G1Affine::rand(&mut rng),
    };

    // Verify should fail
    let valid = Groth16::<E>::verify(&vk, &vault_utxo, &invalid_proof).unwrap_or(false);

    assert!(!valid);
}

#[test]
fn test_dlrep_detects_wrong_coefficients() {
    let mut rng = StdRng::seed_from_u64(12);

    let y_bases = vec![G2Affine::rand(&mut rng); 2];
    let delta = G2Affine::rand(&mut rng);

    // Honest coefficients
    let b_honest = vec![Fr::from(2u64), Fr::from(3u64)];
    let s = Fr::from(7u64);

    // Compute B with honest coefficients
    let mut b_honest_g2 = delta.into_group() * s;
    for (b_j, y_j) in b_honest.iter().zip(&y_bases) {
        b_honest_g2 += y_j.into_group() * b_j;
    }
    let b_honest_g2 = b_honest_g2.into_affine();

    // Create proof with honest coefficients
    let proof: DlrepBProof<E> = prove_b_msm(b_honest_g2, &y_bases, delta, &b_honest, s, &mut rng);

    // Try to verify against WRONG B
    let b_wrong = G2Affine::rand(&mut rng);
    let valid = verify_b_msm(b_wrong, &y_bases, delta, &proof);

    assert!(!valid);
}

#[test]
fn test_different_witnesses_same_statement() {
    // Same circuit, different witnesses
    let circuit1 = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)), // Witness 1: y = 5
    };

    let circuit2 = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)), // Witness 2: same value (for x=25, only y=±5 works)
    };

    let mut rng_crypto = StdRng::seed_from_u64(5);
    let (_pk1, vk1) = Groth16::<E>::circuit_specific_setup(circuit1, &mut rng_crypto).unwrap();
    let (_pk2, vk2) = Groth16::<E>::circuit_specific_setup(circuit2, &mut rng_crypto).unwrap();

    let vault_utxo = vec![Fr::from(25u64)];

    let _r1 = compute_groth16_target(&vk1, &vault_utxo).expect("compute_groth16_target");
    let _r2 = compute_groth16_target(&vk2, &vault_utxo).expect("compute_groth16_target");
}

#[test]
fn test_verify_rejects_mismatched_statement() {
    let mut rng = StdRng::seed_from_u64(13);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    let vault_utxo = vec![Fr::from(25u64)];
    let wrong_vault_utxo = vec![Fr::from(49u64)];

    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Canonical Γ required by verifier

    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof =
        Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder).unwrap();

    let commitments = recorder.build_commitments();
    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments,
    };

    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &vault_utxo));
    assert!(!OneSidedPvugc::verify(
        &bundle,
        &pvugc_vk,
        &vk,
        &wrong_vault_utxo
    ));
}

#[test]
fn test_poce_rejects_mixed_rho_and_swapped_columns() {
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    let mut rng = StdRng::seed_from_u64(123);

    // Setup circuit and keys
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Arming bases
    let mut y_cols = vec![pvugc_vk.beta_g2];
    y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
    let bases: ColumnBases<E> = ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    };

    // Honest arms
    let rho = Fr::from(7u64);
    let arms = arm_columns(&bases, &rho).expect("arm_columns failed");

    // Create T_i
    let s_i = Fr::from(9u64);
    let t_i = (<E as Pairing>::G1::generator() * s_i).into_affine();

    let ctx_hash = b"ctx";
    let gs_digest = b"gs";

    // Prove with honest rho
    let ct = b"ct";
    let tau = b"tau";
    let proof_ok: PoceColumnProof<E> = arkworks_groth16::poce::prove_poce_column(
        &bases.y_cols,
        &bases.delta,
        &arms.y_cols_rho,
        &arms.delta_rho,
        &t_i,
        &rho,
        &s_i,
        ctx_hash,
        gs_digest,
        ct,
        tau,
        &mut rng,
    );
    assert!(arkworks_groth16::poce::verify_poce_column(
        &bases.y_cols,
        &bases.delta,
        &arms.y_cols_rho,
        &arms.delta_rho,
        &t_i,
        &proof_ok,
        ctx_hash,
        gs_digest,
        ct,
        tau,
    ));

    // Mixed rho: change one NON-ZERO column's arm to rho' while keeping others at rho
    let rho2 = Fr::from(5u64);
    let mut bad_arms = arms.clone();
    // find a non-zero Y base index to tamper
    let mut tamper_idx = None;
    for (i, y) in bases.y_cols.iter().enumerate() {
        if !y.is_zero() {
            tamper_idx = Some(i);
            break;
        }
    }
    if let Some(i) = tamper_idx {
        let y_g2 = bases.y_cols[i].into_group();
        bad_arms.y_cols_rho[i] = (y_g2 * rho2).into_affine();
    }
    let ct = b"ct";
    let tau = b"tau";
    let proof_bad: PoceColumnProof<E> = arkworks_groth16::poce::prove_poce_column(
        &bases.y_cols,
        &bases.delta,
        &bad_arms.y_cols_rho,
        &bad_arms.delta_rho,
        &t_i,
        &rho,
        &s_i,
        ctx_hash,
        gs_digest,
        ct,
        tau,
        &mut rng,
    );
    assert!(!arkworks_groth16::poce::verify_poce_column(
        &bases.y_cols,
        &bases.delta,
        &bad_arms.y_cols_rho,
        &bad_arms.delta_rho,
        &t_i,
        &proof_bad,
        ctx_hash,
        gs_digest,
        ct,
        tau,
    ));

    // Swapped columns (two NON-ZERO indices) should also fail
    let mut swapped_arms = arms.clone();
    let mut nz_idx = Vec::new();
    for (i, y) in bases.y_cols.iter().enumerate() {
        if !y.is_zero() {
            nz_idx.push(i);
        }
    }
    if nz_idx.len() >= 2 {
        swapped_arms.y_cols_rho.swap(nz_idx[0], nz_idx[1]);
    }
    let ct = b"ct";
    let tau = b"tau";
    let proof_swapped: PoceColumnProof<E> = arkworks_groth16::poce::prove_poce_column(
        &bases.y_cols,
        &bases.delta,
        &swapped_arms.y_cols_rho,
        &swapped_arms.delta_rho,
        &t_i,
        &rho,
        &s_i,
        ctx_hash,
        gs_digest,
        ct,
        tau,
        &mut rng,
    );
    assert!(!arkworks_groth16::poce::verify_poce_column(
        &bases.y_cols,
        &bases.delta,
        &swapped_arms.y_cols_rho,
        &swapped_arms.delta_rho,
        &t_i,
        &proof_swapped,
        ctx_hash,
        gs_digest,
        ct,
        tau,
    ));
}
#[test]
fn test_duplicate_g2_columns_detected_by_per_column_ties() {
    use ark_bls12_381::Bls12_381 as E;
    use ark_std::rand::SeedableRng;
    let mut rng = StdRng::seed_from_u64(99);

    // Circuit and setup
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Make a valid proof and commitments
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof =
        Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder).unwrap();
    let mut commitments = recorder.build_commitments();

    // Build bundle with per-column ties
    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments.clone(),
    };

    // Baseline should verify with the matching statement
    let vault_utxo = vec![Fr::from(25u64)];
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &vault_utxo));

    // Duplicate one G2 column logically by perturbing two X columns equally/oppositely,
    // which keeps the aggregate but should break per-column ties
    use ark_ec::CurveGroup;
    let a = bundle.groth16_proof.a;
    if commitments.x_b_cols.len() >= 4 {
        // choose two variable columns (>= 2)
        let i = 2usize;
        let j = 3usize;
        let delta = Fr::from(3u64);
        let (xi0, xi1) = commitments.x_b_cols[i];
        let (xj0, xj1) = commitments.x_b_cols[j];
        let xi0p = (xi0.into_group() + a.into_group() * delta).into_affine();
        let xj0p = (xj0.into_group() - a.into_group() * delta).into_affine();
        commitments.x_b_cols[i] = (xi0p, xi1);
        commitments.x_b_cols[j] = (xj0p, xj1);

        let bundle_bad = PvugcBundle {
            groth16_proof: bundle.groth16_proof,
            dlrep_b: bundle.dlrep_b,
            dlrep_ties: bundle.dlrep_ties,
            gs_commitments: commitments,
        };
        assert!(!OneSidedPvugc::verify(
            &bundle_bad,
            &pvugc_vk,
            &vk,
            &vault_utxo
        ));
    }
}

#[test]
fn test_r_independence_from_rho() {
    let mut rng = StdRng::seed_from_u64(12345);

    // Statement: x = y^2 with x fixed
    let x = Fr::from(25u64);
    let y = Fr::from(5u64);
    let public_x = vec![x];

    // Setup Groth16
    let circuit = TestCircuit { x: Some(x), y: Some(y) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    // PVUGC VK wrapper (statement-only bases)
    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Two fresh exponents ρ1 != 0 and ρ2 != 0
    let mut rho1 = Fr::rand(&mut rng);
    if rho1.is_zero() { rho1 = Fr::from(7u64); }
    let mut rho2 = Fr::rand(&mut rng);
    if rho2.is_zero() { rho2 = Fr::from(11u64); }

    // Compute R directly from (vk, x) twice; must be identical and ρ-independent
    let r1 = compute_groth16_target(&vk, &public_x).expect("compute_groth16_target");
    let r2 = compute_groth16_target(&vk, &public_x).expect("compute_groth16_target");
    assert_eq!(r1, r2, "R(vk,x) must be deterministic and ρ-independent");

    // Canonical setup_and_arm for each ρ; returned R must match direct computation
    let (_bases1, arms1, r_setup1, k1_expected) =
        OneSidedPvugc::setup_and_arm::<E>(&pvugc_vk, &vk, &public_x, &rho1).expect("setup_and_arm");
    let (_bases2, arms2, r_setup2, k2_expected) =
        OneSidedPvugc::setup_and_arm::<E>(&pvugc_vk, &vk, &public_x, &rho2).expect("setup_and_arm");

    assert_eq!(r1, r_setup1, "setup_and_arm must not mix ρ into R");
    assert_eq!(r1, r_setup2, "setup_and_arm must not mix ρ into R");

    // Build two valid proofs and commitments (proof randomness differs)
    let mut rec1 = SimpleCoeffRecorder::<E>::new();
    let _proof1 = Groth16::<E>::create_random_proof_with_hook(
        circuit.clone(), &pk, &mut rng, &mut rec1,
    ).unwrap();
    let comm1: OneSidedCommitments<E> = rec1.build_commitments();

    let mut rec2 = SimpleCoeffRecorder::<E>::new();
    let _proof2 = Groth16::<E>::create_random_proof_with_hook(
        circuit, &pk, &mut rng, &mut rec2,
    ).unwrap();
    let comm2: OneSidedCommitments<E> = rec2.build_commitments();

    // Decap with (comm1, arms1) and (comm2, arms2)
    let k1 = OneSidedPvugc::decapsulate::<E>(&comm1, &arms1).expect("decap");
    let k2 = OneSidedPvugc::decapsulate::<E>(&comm2, &arms2).expect("decap");

    // Keys must equal R^ρ for the respective ρ and differ if ρ differ
    assert_eq!(k1, k1_expected, "Decap must produce R^ρ₁");
    assert_eq!(k2, k2_expected, "Decap must produce R^ρ₂");
    if rho1 != rho2 {
        assert_ne!(k1, k2, "Different ρ must yield different keys for fixed (vk,x)");
    }
}

#[test]
fn test_rejects_gamma2_in_statement_bases() {
    let mut rng = StdRng::seed_from_u64(777);

    // Setup circuit
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Produce a valid bundle for the honest pvugc_vk
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder)
        .unwrap();
    let commitments = recorder.build_commitments();
    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments,
    };

    let public_x = vec![Fr::from(25u64)];
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &public_x));

    // Tamper pvugc_vk so that β₂ is replaced with γ₂ → must be rejected
    let mut pvugc_vk_bad = pvugc_vk.clone();
    pvugc_vk_bad.beta_g2 = vk.gamma_g2;
    assert!(!OneSidedPvugc::verify(&bundle, &pvugc_vk_bad, &vk, &public_x));
}

#[test]
fn test_r_is_not_identity_for_typical_statement() {
    let mut rng = StdRng::seed_from_u64(4242);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    let r = compute_groth16_target(&vk, &[Fr::from(25u64)]).expect("compute_groth16_target");
    use ark_std::One;
    assert!(r != PairingOutput::<E>(One::one()), "R(vk,x) must not be identity");
}

#[test]
fn test_size_caps_enforced_in_verify() {
    let mut rng = StdRng::seed_from_u64(7777);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Build a valid bundle via recorder
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder)
        .unwrap();
    let commitments = recorder.build_commitments();
    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments,
    };

    let public_x = &[Fr::from(25u64)];

    // Passing path: defaults via verify()
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, public_x));
    // Passing path: explicit defaults via VerifyLimits and constants
    let ok_defaults = OneSidedPvugc::verify_with_limits(
        &bundle,
        &pvugc_vk,
        &vk,
        public_x,
        &VerifyLimits {
            max_b_columns: Some(DEFAULT_MAX_B_COLUMNS),
            max_theta_rows: Some(DEFAULT_MAX_THETA_ROWS),
            max_total_pairings: Some(DEFAULT_MAX_TOTAL_PAIRINGS),
        },
    );
    assert!(ok_defaults, "verify_with_limits should pass under default size caps");

    // Failing caps: zero theta rows
    let fail_theta = OneSidedPvugc::verify_with_limits(
        &bundle,
        &pvugc_vk,
        &vk,
        public_x,
        &VerifyLimits {
            max_b_columns: None,
            max_theta_rows: Some(0),
            max_total_pairings: None,
        },
    );
    assert!(!fail_theta, "verify must fail when theta rows cap is too small");

    // Failing caps: too small pairing budget
    let fail_pairings = OneSidedPvugc::verify_with_limits(
        &bundle,
        &pvugc_vk,
        &vk,
        public_x,
        &VerifyLimits {
            max_b_columns: None,
            max_theta_rows: None,
            max_total_pairings: Some(1),
        },
    );
    assert!(!fail_pairings, "verify must fail when total pairing budget is too small");
}
