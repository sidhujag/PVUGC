//! SP1 Arming Well-Formedness E2E Test
//!
//! This test exercises the `sp1-arming-wf` guest program end-to-end:
//! - builds a syntactically valid arming package with consistent rho-arms
//! - proves + verifies the SP1 proof for that package
//! - checks that common "bricking" mutations are rejected by the guest
//!
//! This is an integration test and is intentionally `#[ignore]` because it requires:
//! - SP1 toolchain / prover runtime available
//! - a built guest ELF provided via env var
//!
//! Run (example):
//!   RUSTFLAGS="-C target-cpu=native" \
//!   cargo test --release test_sp1_arming_wf_no_bricking -- --ignored --nocapture

use ark_bw6_761::BW6_761;
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, Field, One, PrimeField, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{rngs::StdRng, RngCore, SeedableRng};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use sp1_sdk::{ProverClient, SP1Stdin};

use arkworks_groth16::ct::{ad_core_digest, compute_key_commitment_tag, DemP2};
use arkworks_groth16::poce::{prove_poce_column, verify_poce_column, PoceColumnProof};
use arkworks_groth16::sp1_arming_wf::{
    accept_package_with_committed_digest, ArmingWfPackagePublicBytes,
};
use arkworks_groth16::bitcoin::{
    ArrayEncoding, PrimeCurveAffine, Reduce, ToEncodedPoint, AffinePoint, ProjectivePoint, Scalar,
    U256,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackagePublic {
    pub profile: Vec<u8>,
    pub delta_base: Vec<u8>,
    pub delta_arm: Vec<u8>,
    pub r_baked: Vec<u8>,
    pub ad_digest: [u8; 32],
    pub ciphertext: Vec<u8>,
    pub tau: [u8; 32],
    pub t_i_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackageWitness {
    pub rho: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfInput {
    pub public: ArmingPackagePublic,
    pub witness: ArmingPackageWitness,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfOutput {
    pub pkg_digest: [u8; 32],
}

/// Simple test-only env var guard (mirrors `tests/test_sp1_e2e.rs`).
struct EnvVarGuard {
    key: &'static str,
    old: Option<std::ffi::OsString>,
}

impl EnvVarGuard {
    fn set(key: &'static str, value: &str) -> Self {
        let old = std::env::var_os(key);
        std::env::set_var(key, value);
        Self { key, old }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match &self.old {
            Some(v) => std::env::set_var(self.key, v),
            None => std::env::remove_var(self.key),
        }
    }
}

fn sha256_bytes(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}

fn serialize_bytes_len_prefixed(out: &mut Vec<u8>, v: &[u8]) {
    let len_u32: u32 = v
        .len()
        .try_into()
        .expect("vector too large to length-prefix");
    out.extend_from_slice(&len_u32.to_le_bytes());
    out.extend_from_slice(v);
}

const BW6_FQ_BYTES: usize = 96;

fn bw6_fq_to_le_96_bytes(x: &ark_bw6_761::Fq) -> [u8; BW6_FQ_BYTES] {
    let mut out = [0u8; BW6_FQ_BYTES];
    let le = x.into_bigint().to_bytes_le();
    out[..le.len()].copy_from_slice(&le);
    out
}

fn bw6_g2_affine_to_xy_bytes(p: &<BW6_761 as Pairing>::G2Affine) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 * BW6_FQ_BYTES);
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&p.x));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&p.y));
    out
}

fn bw6_gt_to_fq6_bytes(x: &<BW6_761 as Pairing>::TargetField) -> Vec<u8> {
    // Must match `sp1-arming-wf/program/src/bw6_syscall.rs::Fq6::to_bytes_le_vec`.
    let mut out = Vec::with_capacity(6 * BW6_FQ_BYTES);
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c0.c0));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c0.c1));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c0.c2));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c1.c0));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c1.c1));
    out.extend_from_slice(&bw6_fq_to_le_96_bytes(&x.c1.c2));
    out
}

/// Must match `sp1-arming-wf/program/src/main.rs::encode_public`.
fn encode_public(pkg: &ArmingPackagePublic) -> Vec<u8> {
    let mut out = Vec::new();
    serialize_bytes_len_prefixed(&mut out, &pkg.profile);

    serialize_bytes_len_prefixed(&mut out, &pkg.delta_base);
    serialize_bytes_len_prefixed(&mut out, &pkg.delta_arm);
    serialize_bytes_len_prefixed(&mut out, &pkg.r_baked);
    out.extend_from_slice(&pkg.ad_digest);
    serialize_bytes_len_prefixed(&mut out, &pkg.ciphertext);
    out.extend_from_slice(&pkg.tau);
    serialize_bytes_len_prefixed(&mut out, &pkg.t_i_bytes);

    out
}

fn load_arming_wf_elf() -> Vec<u8> {
    // Preferred: committed ELF blob in the repo.
    let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let committed = repo_root
        .join("sp1-arming-wf")
        .join("elf")
        .join("pvugc-sp1-arming-wf-program.elf");

    // Fallback: env override.
    let env_override = std::env::var("PVUGC_SP1_ARMING_WF_ELF").ok();

    let p = env_override
        .as_ref()
        .map(std::path::PathBuf::from)
        .unwrap_or(committed.clone());

    std::fs::read(&p).unwrap_or_else(|e| {
        panic!(
            "failed to read SP1 arming-wf ELF at {}\n\
             - to use a custom path: set PVUGC_SP1_ARMING_WF_ELF=/abs/path/to/elf\n\
             - to use the committed path: build the guest and commit/copy it to {}\n\
             error: {e}",
            p.display(),
            committed.display()
        )
    })
}

#[derive(Clone)]
struct ArmingArtifacts {
    input: ArmingWfInput,
    // Typed objects for outside checks.
    delta_base: <BW6_761 as Pairing>::G2Affine,
    delta_arm: <BW6_761 as Pairing>::G2Affine,
    // Minimal column set for PoCE (test-only).
    y_bases: Vec<<BW6_761 as Pairing>::G2Affine>,
    y_arms: Vec<<BW6_761 as Pairing>::G2Affine>,
    t_i_pairing: <BW6_761 as Pairing>::G1Affine,
    poce: PoceColumnProof<BW6_761>,
    // Bind all outside proofs to the exact SP1 public package encoding.
    pkg_digest: [u8; 32],
    // PoCE binds these separately (mirrors production API).
    ctx_hash: [u8; 32],
    gs_digest: [u8; 32],
}

fn build_valid_artifacts(rng: &mut StdRng) -> ArmingArtifacts {
    type E = BW6_761;

    // Random nonzero rho.
    let mut rho = <E as Pairing>::ScalarField::rand(rng);
    while rho.is_zero() {
        rho = <E as Pairing>::ScalarField::rand(rng);
    }
    let mut rho_bytes = Vec::new();
    rho.serialize_compressed(&mut rho_bytes).expect("rho serialize");

    // delta base/arm in G2 (outer pairing curve).
    let delta_base = (<E as Pairing>::G2::generator() * <E as Pairing>::ScalarField::rand(rng))
        .into_affine();
    let delta_arm = (delta_base.into_group() * rho).into_affine();

    // Any non-degenerate R in GT works for test; in production this is R_baked(vk, x).
    let r_baked = E::pairing(<E as Pairing>::G1::generator(), <E as Pairing>::G2::generator()).0;
    assert!(!r_baked.is_zero());
    assert!(!r_baked.is_one());

    // K = R^rho, encoded as raw Fq6 tower limbs (must match guest semantics).
    let k = r_baked.pow(&rho.into_bigint());
    let k_bytes = bw6_gt_to_fq6_bytes(&k);

    // AD_core bytes are not needed by the guest, only ad_digest.
    // In production, ad_digest binds the full AD_core transcript; here we just pick a fixed blob.
    let ad_core = b"PVUGC/test/ad_core/v1".to_vec();
    let ad_digest = ad_core_digest(&ad_core);

    // Plaintext is a 32-byte secp scalar (big-endian) corresponding to the public adaptor point T_i.
    let mut plaintext = [0u8; 32];
    rng.fill_bytes(&mut plaintext);
    if plaintext == [0u8; 32] {
        plaintext[31] = 1;
    }

    // Compute T_i bytes using k256 SEC1 compressed encoding to match the guest check.
    //
    // NOTE: `Scalar::reduce` reduces the 32 bytes mod curve order, matching PVUGC semantics.
    let s = Scalar::reduce(U256::from_be_byte_array(plaintext.into()));
    let t_proj = ProjectivePoint::GENERATOR * s;
    let t_aff = AffinePoint::from(t_proj);
    assert!(
        !bool::from(t_aff.is_identity()),
        "avoid identity T_i in test"
    );
    let t_i_bytes = t_aff.to_encoded_point(true).as_bytes().to_vec();
    assert_eq!(t_i_bytes.len(), 33, "SEC1 compressed point must be 33 bytes");

    // DEM encrypt + tag.
    let dem = DemP2::new(&k_bytes, &ad_core);
    let ciphertext = dem.encrypt(&plaintext);
    assert_eq!(ciphertext.len(), 32);
    let tau = compute_key_commitment_tag(&k_bytes, &ad_core, &ciphertext);

    // Serialize delta/R for package binding (zkvm-friendly raw limb encodings).
    let delta_base_bytes = bw6_g2_affine_to_xy_bytes(&delta_base);
    let delta_arm_bytes = bw6_g2_affine_to_xy_bytes(&delta_arm);
    let r_baked_bytes = bw6_gt_to_fq6_bytes(&r_baked);

    let public = ArmingPackagePublic {
        profile: b"PVUGC/SP1/arming_wf/test".to_vec(),
        delta_base: delta_base_bytes,
        delta_arm: delta_arm_bytes,
        r_baked: r_baked_bytes,
        ad_digest,
        ciphertext,
        tau,
        t_i_bytes,
    };

    let input = ArmingWfInput {
        public,
        witness: ArmingPackageWitness { rho: rho_bytes },
    };

    let pkg_digest = sha256_bytes(&[&encode_public(&input.public)]);

    // --- Outside checks: PoCE ---
    // Keep PoCE small in tests (1 "public" + 1 witness basis).
    let y_bases: Vec<<E as Pairing>::G2Affine> = vec![
        (<E as Pairing>::G2::generator() * <E as Pairing>::ScalarField::rand(rng)).into_affine(),
        (<E as Pairing>::G2::generator() * <E as Pairing>::ScalarField::rand(rng)).into_affine(),
    ];
    let y_arms: Vec<<E as Pairing>::G2Affine> = y_bases
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();

    // PoCE's (pairing-curve) adaptor-share commitment is orthogonal to Bitcoin secp share.
    let s_i = <E as Pairing>::ScalarField::rand(rng);
    let t_i_pairing = (<E as Pairing>::G1::generator() * s_i).into_affine();

    // Bind these like production does (ctx_hash + gs_digest + ct + tau).
    // For this test, we derive ctx_hash and gs_digest from pkg_digest to ensure linkage.
    let ctx_hash = sha256_bytes(&[b"PVUGC/test/ctx_hash", &pkg_digest]);
    let gs_digest = sha256_bytes(&[b"PVUGC/test/gs_digest", &pkg_digest]);

    let poce = prove_poce_column::<E, _>(
        &y_bases,
        &delta_base,
        &y_arms,
        &delta_arm,
        &t_i_pairing,
        &rho,
        &s_i,
        &ctx_hash,
        &gs_digest,
        &input.public.ciphertext,
        &input.public.tau,
        rng,
    );

    ArmingArtifacts {
        input,
        delta_base,
        delta_arm,
        y_bases,
        y_arms,
        t_i_pairing,
        poce,
        pkg_digest,
        ctx_hash,
        gs_digest,
    }
}

#[test]
#[ignore]
fn test_sp1_arming_wf_no_bricking() {
    // Force local CPU prover + dev artifacts for this test run.
    let _sp1_dev = EnvVarGuard::set("SP1_DEV", "1");
    let _sp1_prover = EnvVarGuard::set("SP1_PROVER", "cpu");
    let _sp1_allow_deprecated_hooks = EnvVarGuard::set("SP1_ALLOW_DEPRECATED_HOOKS", "true");

    let elf = load_arming_wf_elf();
    let client = ProverClient::from_env();
    let (pk, vk) = client.setup(&elf);

    let mut rng = StdRng::seed_from_u64(20260223);
    let t_build = std::time::Instant::now();
    let artifacts = build_valid_artifacts(&mut rng);
    println!("[sp1-arming-wf] build input/proofs time: {:?}", t_build.elapsed());
    let input = artifacts.input.clone();

    // --- Happy path: prove + verify ---
    let mut stdin = SP1Stdin::new();
    stdin.write(&input);

    // Execute first so we can report "how big" it is in zkVM terms.
    // (SP1 is STARK-based; there is no R1CS constraint count, but instruction/syscall counts are
    // good concrete proxies.)
    let t_exec = std::time::Instant::now();
    let (_pv, report) = client
        .execute(&elf, &stdin)
        .run()
        .expect("arming-wf execute failed");
    println!("\n[sp1-arming-wf] execute time: {:?}", t_exec.elapsed());
    println!(
        "[sp1-arming-wf] total instructions: {} | total syscalls: {}",
        report.total_instruction_count(),
        report.total_syscall_count()
    );
    println!("[sp1-arming-wf] execution report:\n{report}");
    println!("[sp1-arming-wf] cycle tracker: {:?}", report.cycle_tracker);

    // When profiling guest hotspots, avoid spending ~minutes proving a STARK.
    // Run with: PVUGC_SP1_ARMING_WF_SKIP_PROVE=1
    if std::env::var("PVUGC_SP1_ARMING_WF_SKIP_PROVE").ok().as_deref() == Some("1") {
        return;
    }

    // Use a STARK proof mode (no SNARK wrapping / no ceremony).
    // `core()` is much faster than `compressed()` since it avoids recursive aggregation.
    let t_prove = std::time::Instant::now();
    let mut proof = client
        .prove(&pk, &stdin)
        .core()
        .run()
        .expect("arming-wf prove failed");
    println!("[sp1-arming-wf] prove time: {:?}", t_prove.elapsed());
    client.verify(&proof, &vk).expect("arming-wf verify failed");

    // Output binding: committed pkg_digest must match sha256(encode_public).
    let out = proof.public_values.read::<ArmingWfOutput>();
    assert_eq!(out.pkg_digest, artifacts.pkg_digest);

    // Outside-SP1 hygiene + digest binding (GPT Pro checklist):
    // - parse/validate delta points and r_baked from the *raw bytes format*
    // - recompute pkg_digest over those exact bytes and ensure it matches the SP1 commitment
    let audited = accept_package_with_committed_digest(
        ArmingWfPackagePublicBytes {
            profile: input.public.profile.clone(),
            delta_base: input.public.delta_base.clone(),
            delta_arm: input.public.delta_arm.clone(),
            r_baked: input.public.r_baked.clone(),
            ad_digest: input.public.ad_digest,
            ciphertext: input.public.ciphertext.clone(),
            tau: input.public.tau,
            t_i_bytes: input.public.t_i_bytes.clone(),
        },
        &out.pkg_digest,
    )
    .expect("outside-SP1 arming-wf package audit must accept");
    // Sanity: audited digest should equal the SP1-committed digest.
    assert_eq!(audited.pkg_digest, out.pkg_digest);

    // Negative sanity: if the received bytes differ from the bytes committed by SP1,
    // acceptance must fail even if the SP1 proof verifies.
    {
        let mut mutated = audited.pkg.clone();
        mutated.ciphertext[0] ^= 1;
        let res = accept_package_with_committed_digest(mutated, &out.pkg_digest);
        assert!(res.is_err(), "outside-SP1 audit accepted pkg_digest mismatch");
    }

    // Outside validation: PoCE must verify, and we log timings.
    let t_poce = std::time::Instant::now();
    let poce_ok = verify_poce_column::<BW6_761>(
        &artifacts.y_bases,
        &artifacts.delta_base,
        &artifacts.y_arms,
        &artifacts.delta_arm,
        &artifacts.t_i_pairing,
        &artifacts.poce,
        &artifacts.ctx_hash,
        &artifacts.gs_digest,
        &input.public.ciphertext,
        &input.public.tau,
    );
    println!("[sp1-arming-wf] poce verify time: {:?}", t_poce.elapsed());
    assert!(poce_ok, "poce verification failed (should be valid)");

    // --- Negative cases: cheap execute() checks ---
    fn should_reject<F: FnOnce(&mut ArmingWfInput)>(
        client: &sp1_sdk::EnvProver,
        elf: &[u8],
        input: &ArmingWfInput,
        label: &str,
        f: F,
    ) {
        let mut bad = input.clone();
        f(&mut bad);
        let mut stdin = SP1Stdin::new();
        stdin.write(&bad);
        let res = client.execute(elf, &stdin).run();
        assert!(res.is_err(), "guest accepted bricking mutation: {label}");
    }

    // 1) Wrong tau (tag mismatch) => reject
    should_reject(&client, &elf, &input, "wrong_tau", |bad| {
        bad.public.tau[0] ^= 1;
    });

    // 2) Wrong ciphertext (decrypts differently; should also break tau) => reject
    should_reject(&client, &elf, &input, "wrong_ct", |bad| {
        bad.public.ciphertext[0] ^= 1;
    });

    // 3) Wrong adaptor commitment T_i => reject even if tau/ct are consistent with K
    should_reject(&client, &elf, &input, "wrong_t_i_bytes", |bad| {
        bad.public.t_i_bytes[0] ^= 1;
    });

    // 4) Wrong delta_arm => reject (rho no longer matches the published arm).
    should_reject(&client, &elf, &input, "wrong_delta_arm", |bad| {
        bad.public.delta_arm[0] ^= 1;
    });

    // 5) Wrong r_baked => reject (derived K changes, causing tag mismatch).
    should_reject(&client, &elf, &input, "wrong_r_baked", |bad| {
        bad.public.r_baked[0] ^= 1;
    });

    // 6) rho=0 in witness => reject
    should_reject(&client, &elf, &input, "rho_zero", |bad| {
        let zero = <BW6_761 as Pairing>::ScalarField::zero();
        let mut bytes = Vec::new();
        zero.serialize_compressed(&mut bytes).unwrap();
        bad.witness.rho = bytes;
    });

    // 6b) ciphertext length mismatch => reject
    should_reject(&client, &elf, &input, "ct_len_31", |bad| {
        bad.public.ciphertext = bad.public.ciphertext[..31].to_vec();
    });
    should_reject(&client, &elf, &input, "ct_len_33", |bad| {
        let mut ct = bad.public.ciphertext.clone();
        ct.push(0u8);
        bad.public.ciphertext = ct;
    });

    // 6c) t_i_bytes malformed => reject
    should_reject(&client, &elf, &input, "t_i_len_32", |bad| {
        bad.public.t_i_bytes = bad.public.t_i_bytes[..32].to_vec();
    });
    should_reject(&client, &elf, &input, "t_i_bad_prefix", |bad| {
        bad.public.t_i_bytes[0] = 0x04; // invalid for SEC1 compressed
    });

    // 6d) malformed encodings (wrong lengths) for BW6 elements => reject on deserialize.
    should_reject(&client, &elf, &input, "delta_base_len_bad", |bad| {
        bad.public.delta_base = bad.public.delta_base[..(bad.public.delta_base.len() - 1)].to_vec();
    });
    should_reject(&client, &elf, &input, "r_baked_len_bad", |bad| {
        bad.public.r_baked = bad.public.r_baked[..(bad.public.r_baked.len() - 1)].to_vec();
    });

    // 7) Wrong y_arm (not part of SP1 input) => PoCE must reject.
    {
        let mut bad = artifacts.clone();
        bad.y_arms[0] = (bad.y_arms[0].into_group() + <BW6_761 as Pairing>::G2::generator()).into_affine();
        assert!(
            !verify_poce_column::<BW6_761>(
                &bad.y_bases,
                &bad.delta_base,
                &bad.y_arms,
                &bad.delta_arm,
                &bad.t_i_pairing,
                &bad.poce,
                &bad.ctx_hash,
                &bad.gs_digest,
                &bad.input.public.ciphertext,
                &bad.input.public.tau,
            ),
            "poce should reject mismatched y_arm"
        );
    }

    // 8) Wrong ctx_hash => PoCE must reject (transcript binding).
    {
        let mut bad = artifacts.clone();
        bad.ctx_hash[0] ^= 1;
        assert!(
            !verify_poce_column::<BW6_761>(
                &bad.y_bases,
                &bad.delta_base,
                &bad.y_arms,
                &bad.delta_arm,
                &bad.t_i_pairing,
                &bad.poce,
                &bad.ctx_hash,
                &bad.gs_digest,
                &bad.input.public.ciphertext,
                &bad.input.public.tau,
            ),
            "poce should reject mismatched ctx_hash"
        );
    }
}

