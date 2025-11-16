//! Targeted mutation checks around `OneSidedPvugc::verify`.
//! This exercises a few structured tamperings of otherwise-valid bundles
//! to ensure the verifier rejects manipulated artifacts.

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use ark_std::{
    rand::rngs::StdRng,
    rand::{RngCore, SeedableRng},
    UniformRand,
};
use sha2::{Digest, Sha256};

use arkworks_groth16::{
    api::enforce_public_inputs_are_outputs,
    coeff_recorder::{BCoefficients, SimpleCoeffRecorder},
    ct::{serialize_gt, AdCore, DemP2},
    ctx::PvugcContextBuilder,
    ppe::PvugcVk,
    secp256k1::{compress_secp_point, scalar_bytes_to_point},
    ColumnArmingAttestation, OneSidedPvugc, PvugcBundle,
};

type PairingE = E;

#[derive(Clone)]
struct SquareCircuit {
    x: Option<Fr>,
    y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SquareCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        x_var.enforce_equal(&(y_var.clone() * y_var))?;
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

struct Fixture {
    bundle: PvugcBundle<PairingE>,
    pvugc_vk: PvugcVk<PairingE>,
    vk: ark_groth16::VerifyingKey<PairingE>,
    public_inputs: Vec<Fr>,
    coeffs: BCoefficients<Fr>,
    column_arms: arkworks_groth16::arming::ColumnArms<PairingE>,
    honest_key: ark_ec::pairing::PairingOutput<PairingE>,
    bases: arkworks_groth16::arming::ColumnBases<PairingE>,
    t_i: <PairingE as Pairing>::G1Affine,
    ctx_hash: [u8; 32],
    gs_digest: [u8; 32],
    ad_core_bytes: Vec<u8>,
    ciphertext: Vec<u8>,
    tau: [u8; 32],
    column_attestation: ColumnArmingAttestation<PairingE>,
}

fn clone_bundle(input: &PvugcBundle<PairingE>) -> PvugcBundle<PairingE> {
    PvugcBundle {
        groth16_proof: input.groth16_proof.clone(),
        dlrep_b: input.dlrep_b.clone(),
        dlrep_ties: input.dlrep_ties.clone(),
        gs_commitments: arkworks_groth16::OneSidedCommitments {
            x_b_cols: input.gs_commitments.x_b_cols.clone(),
            theta: input.gs_commitments.theta.clone(),
            theta_delta_cancel: input.gs_commitments.theta_delta_cancel,
        },
    }
}

fn derive_label(seed: u64, label: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(label);
    hasher.update(&seed.to_le_bytes());
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn serialize_column_arms(arms: &arkworks_groth16::arming::ColumnArms<PairingE>) -> Vec<u8> {
    let mut buf = Vec::new();
    arms.serialize_compressed(&mut buf).unwrap();
    buf
}

fn build_fixture(seed: u64) -> Fixture {
    let mut rng = StdRng::seed_from_u64(seed);
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    let (pk, vk) = Groth16::<PairingE>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let public_inputs = vec![Fr::from(25u64)];

    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    let rho = Fr::rand(&mut rng);
    let (bases, column_arms, _r, honest_key) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &public_inputs, &rho).unwrap();

    let mut recorder = SimpleCoeffRecorder::<PairingE>::new();
    recorder.set_num_instance_variables(vk.gamma_abc_g1.len());
    let proof =
        Groth16::<PairingE>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder)
            .unwrap();

    let commitments = recorder.build_commitments();
    let s_i = Fr::rand(&mut rng);
    let t_i = (<PairingE as Pairing>::G1::generator() * s_i).into_affine();
    let mut secp_scalar = [0u8; 32];
    rng.fill_bytes(&mut secp_scalar);
    let secp_point = scalar_bytes_to_point(&secp_scalar);
    let secp_bytes = compress_secp_point(&secp_point);
    let secp_agg_bytes = secp_bytes.clone();

    let vk_hash = derive_label(seed, b"vk_hash");
    let x_hash = derive_label(seed, b"x_hash");
    let mut y_cols_hasher = Sha256::new();
    y_cols_hasher.update(b"PVUGC/YCOLS");
    for col in &bases.y_cols {
        let mut buf = Vec::new();
        col.serialize_compressed(&mut buf).unwrap();
        y_cols_hasher.update(&buf);
    }
    let y_cols_digest: [u8; 32] = y_cols_hasher.finalize().into();
    let epoch_nonce = derive_label(seed, b"epoch_nonce");
    let tapleaf_hash = derive_label(seed, b"tapleaf_hash");
    let gs_digest = derive_label(seed, b"gs_digest");

    let ctx = PvugcContextBuilder::new(vk_hash, x_hash, y_cols_digest, epoch_nonce)
        .with_tapleaf(tapleaf_hash, 0xc0)
        .with_path_tag("compute")
        .finalize(None, None);
    let ctx_hash = ctx.ctx_hash;

    let bases_bytes = serialize_column_arms(&column_arms);
    let mut delta_bytes = Vec::new();
    column_arms
        .delta_rho
        .serialize_compressed(&mut delta_bytes)
        .unwrap();

    let ad_core = AdCore::new(
        vk_hash,
        x_hash,
        ctx_hash,
        tapleaf_hash,
        0xc0,
        bases_bytes.clone(), // reuse as tx template placeholder
        "compute",
        0,
        secp_bytes.clone(),
        secp_agg_bytes.clone(),
        bases_bytes.clone(),
        delta_bytes.clone(),
        gs_digest,
    );
    let ad_core_bytes = ad_core.serialize();

    let k_bytes = serialize_gt::<PairingE>(&honest_key.0);
    let dem = DemP2::new(&k_bytes, &ad_core_bytes);
    let plaintext = secp_scalar.to_vec();
    let ciphertext = dem.encrypt(&plaintext);
    let tau =
        OneSidedPvugc::compute_key_commitment_tag_dem(&honest_key, &ad_core_bytes, &ciphertext);

    let column_attestation = OneSidedPvugc::attest_column_arming(
        &bases,
        &column_arms,
        &t_i,
        &rho,
        &s_i,
        &honest_key,
        &ad_core_bytes,
        &ctx_hash,
        &gs_digest,
        &ciphertext,
        &tau,
        &mut rng,
    )
    .expect("column attestation");

    let coeffs = recorder
        .get_coefficients()
        .expect("coefficients must be recorded");

    let bundle = PvugcBundle {
        groth16_proof: proof,
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &vk, &public_inputs, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments,
    };
    let mut actual_public_leg = pvugc_vk.beta_g2.into_group();
    actual_public_leg += pvugc_vk.b_g2_query[0].into_group();
    for (idx, coeff) in coeffs.b.iter().take(public_inputs.len()).enumerate() {
        let base = pvugc_vk.b_g2_query[1 + idx];
        actual_public_leg += base.into_group() * coeff;
    }
    assert_eq!(
        actual_public_leg.into_affine(),
        bases.y_cols[0],
        "column bases public leg mismatch"
    );

    // Sanity: reconstruct B directly from recorded coefficients
    let mut reconstructed_b = pvugc_vk.beta_g2.into_group();
    reconstructed_b += pvugc_vk.b_g2_query[0].into_group(); // implicit 1-wire
    for (coeff, base) in coeffs.b.iter().zip(pvugc_vk.b_g2_query.iter().skip(1)) {
        reconstructed_b += base.into_group() * coeff;
    }
    reconstructed_b += pvugc_vk.delta_g2.into_group() * coeffs.s;
    assert_eq!(
        reconstructed_b.into_affine(),
        bundle.groth16_proof.b,
        "hooked coefficients failed to reassemble B"
    );

    Fixture {
        bundle,
        pvugc_vk,
        vk,
        public_inputs,
        column_arms,
        honest_key,
        bases,
        t_i,
        ctx_hash,
        gs_digest,
        ad_core_bytes,
        ciphertext,
        tau,
        column_attestation,
        coeffs,
    }
}

#[test]
fn verify_rejects_mutated_bundles() {
    for offset in 0u64..8 {
        let seed = 0xF1AFA2_u64 + offset;
        let Fixture {
            bundle,
            pvugc_vk,
            vk,
            public_inputs,
            column_arms,
            honest_key,
            bases,
            coeffs,
            ..
        } = build_fixture(seed);

        assert!(
            Groth16::<PairingE>::verify(&vk, &public_inputs, &bundle.groth16_proof).unwrap(),
            "baseline Groth16 proof must verify"
        );
        let public_leg = bases
            .y_cols
            .first()
            .expect("column bases must include public leg");
        let witness_cols = &bases.y_cols[1..];
        let b_prime = (bundle.groth16_proof.b.into_group() - public_leg.into_group()).into_affine();
        let mut reconstructed = pvugc_vk.delta_g2.into_group() * coeffs.s;
        let public_count = vk.gamma_abc_g1.len().saturating_sub(1);
        for (coeff, base) in coeffs.b.iter().skip(public_count).zip(witness_cols.iter()) {
            reconstructed += base.into_group() * coeff;
        }
        assert_eq!(
            reconstructed.into_affine(),
            b_prime,
            "reconstructed B' mismatch"
        );
        assert_eq!(
            bundle.dlrep_b.responses.len(),
            witness_cols.len() + 1,
            "dlrep response length mismatch"
        );
        assert!(
            arkworks_groth16::dlrep::verify_b_msm::<PairingE>(
                b_prime,
                witness_cols,
                pvugc_vk.delta_g2,
                &bundle.dlrep_b
            ),
            "baseline DLREP_B must verify"
        );
        let mut x_cols = Vec::new();
        for (i, (x0, _)) in bundle.gs_commitments.x_b_cols.iter().enumerate() {
            if i == 0 {
                continue;
            }
            x_cols.push(*x0);
        }
        assert!(
            arkworks_groth16::dlrep::verify_ties_per_column::<PairingE>(
                bundle.groth16_proof.a,
                &x_cols,
                &bundle.dlrep_ties,
                bundle.dlrep_b.commitment
            ),
            "baseline tie proof must verify"
        );
        let baseline_ok = OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &public_inputs);
        assert!(
            baseline_ok,
            "baseline bundle must verify (|X|={}, |Y|={})",
            bundle.gs_commitments.x_b_cols.len(),
            column_arms.y_cols_rho.len(),
        );
        let expected_key =
            OneSidedPvugc::decapsulate(&bundle.gs_commitments, &column_arms).expect("decap");
        assert_eq!(expected_key, honest_key, "baseline key mismatch");

        let mut rng = StdRng::seed_from_u64(seed.wrapping_mul(0xA5A5_5A5A_u64));

        let mutations: Vec<(&str, Box<dyn Fn(&mut PvugcBundle<PairingE>, &mut StdRng)>)> = vec![
            (
                "tamper_groth16_a",
                Box::new(|b, r| {
                    b.groth16_proof.a = (<PairingE as Pairing>::G1::rand(r)).into_affine();
                }),
            ),
            (
                "tamper_groth16_c",
                Box::new(|b, r| {
                    b.groth16_proof.c = (<PairingE as Pairing>::G1::rand(r)).into_affine();
                }),
            ),
            (
                "shuffle_first_commitment",
                Box::new(|b, r| {
                    let random = (<PairingE as Pairing>::G1::rand(r)).into_affine();
                    if let Some(first) = b.gs_commitments.x_b_cols.first_mut() {
                        first.0 = random;
                    }
                }),
            ),
            (
                "invalidate_theta",
                Box::new(|b, r| {
                    if let Some(theta) = b.gs_commitments.theta.get_mut(0) {
                        theta.1 = (<PairingE as Pairing>::G1::rand(r)).into_affine();
                    }
                }),
            ),
            (
                "alter_dlrep_response",
                Box::new(|b, r| {
                    if let Some(resp) = b.dlrep_b.responses.get_mut(0) {
                        *resp += <PairingE as Pairing>::ScalarField::rand(r);
                    }
                }),
            ),
            (
                "alter_tie_response",
                Box::new(|b, r| {
                    if let Some(resp) = b.dlrep_ties.responses.get_mut(0) {
                        *resp += <PairingE as Pairing>::ScalarField::rand(r);
                    }
                }),
            ),
        ];

        for (label, mutate) in mutations {
            let mut tampered = clone_bundle(&bundle);
            mutate(&mut tampered, &mut rng);
            assert!(
                !OneSidedPvugc::verify(&tampered, &pvugc_vk, &vk, &public_inputs),
                "mutation {label} unexpectedly verified"
            );
        }
    }
}

#[test]
fn poce_cross_session_replay_fails() {
    let seeds = [
        (0xABCDEF01_u64, 0x13572468_u64),
        (0x11111111_u64, 0x22222222_u64),
        (0x33333333_u64, 0x44444444_u64),
    ];

    for (seed_a, seed_b) in seeds {
        let fixture_a = build_fixture(seed_a);
        let fixture_b = build_fixture(seed_b);

        assert!(
            OneSidedPvugc::verify_column_arming(
                &fixture_a.bases,
                &fixture_a.column_arms,
                &fixture_a.t_i,
                &fixture_a.column_attestation,
                &fixture_a.ad_core_bytes,
                &fixture_a.ctx_hash,
                &fixture_a.gs_digest,
                &fixture_a.ciphertext,
                &fixture_a.tau,
            ),
            "baseline attestation must succeed"
        );

        let tamper_cases = vec![
            (
                "replay_with_other_ctx_hash",
                fixture_b.ctx_hash,
                fixture_a.gs_digest,
                fixture_a.ciphertext.clone(),
                fixture_a.tau,
                fixture_a.bases.clone(),
                fixture_a.column_arms.clone(),
            ),
            (
                "replay_with_other_gs_digest",
                fixture_a.ctx_hash,
                fixture_b.gs_digest,
                fixture_a.ciphertext.clone(),
                fixture_a.tau,
                fixture_a.bases.clone(),
                fixture_a.column_arms.clone(),
            ),
            (
                "swap_ciphertext_and_tau",
                fixture_a.ctx_hash,
                fixture_a.gs_digest,
                fixture_b.ciphertext.clone(),
                fixture_b.tau,
                fixture_a.bases.clone(),
                fixture_a.column_arms.clone(),
            ),
            (
                "swap_column_arms",
                fixture_a.ctx_hash,
                fixture_a.gs_digest,
                fixture_a.ciphertext.clone(),
                fixture_a.tau,
                fixture_b.bases.clone(),
                fixture_b.column_arms.clone(),
            ),
        ];

        for (label, ctx_hash, gs_digest, ciphertext, tau, bases, column_arms) in tamper_cases {
            assert!(
                !OneSidedPvugc::verify_column_arming(
                    &bases,
                    &column_arms,
                    &fixture_a.t_i,
                    &fixture_a.column_attestation,
                    &fixture_a.ad_core_bytes,
                    &ctx_hash,
                    &gs_digest,
                    &ciphertext,
                    &tau,
                ),
                "Column attestation unexpectedly succeeded for case {label}"
            );
        }
    }
}

#[test]
fn dem_tag_binding_checks_metadata() {
    for seed in [0x42424242_u64, 0x51515151_u64, 0x61616161_u64] {
        let fixture = build_fixture(seed);

        let derived_key = fixture.honest_key;
        let ok = OneSidedPvugc::verify_key_commitment_dem::<PairingE>(
            &derived_key,
            &fixture.ad_core_bytes,
            &fixture.ciphertext,
            &fixture.tau,
        );
        assert!(ok, "baseline verify_key_commitment_dem should succeed");

        let mut wrong_ad = fixture.ad_core_bytes.clone();
        if let Some(first) = wrong_ad.first_mut() {
            *first ^= 0x01;
        }
        assert!(
            !OneSidedPvugc::verify_key_commitment_dem::<PairingE>(
                &derived_key,
                &wrong_ad,
                &fixture.ciphertext,
                &fixture.tau,
            ),
            "ad_core mutation must be rejected"
        );

        let mut wrong_ct = fixture.ciphertext.clone();
        if let Some(first) = wrong_ct.first_mut() {
            *first ^= 0x02;
        }
        assert!(
            !OneSidedPvugc::verify_key_commitment_dem::<PairingE>(
                &derived_key,
                &fixture.ad_core_bytes,
                &wrong_ct,
                &fixture.tau,
            ),
            "ciphertext mutation must be rejected"
        );

        let mut wrong_tau = fixture.tau;
        wrong_tau[0] ^= 0x04;
        assert!(
            !OneSidedPvugc::verify_key_commitment_dem::<PairingE>(
                &derived_key,
                &fixture.ad_core_bytes,
                &fixture.ciphertext,
                &wrong_tau,
            ),
            "modified tau must be rejected"
        );

        let recomputed = OneSidedPvugc::compute_key_commitment_tag_dem(
            &derived_key,
            &fixture.ad_core_bytes,
            &fixture.ciphertext,
        );
        assert_eq!(
            recomputed, fixture.tau,
            "tag recomputation should match published tau"
        );
    }
}
