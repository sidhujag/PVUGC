#![no_main]
sp1_zkvm::entrypoint!(main);

mod bw6_syscall;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use ark_bw6_761::Fr as Bw6Fr;
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_serialize::CanonicalDeserialize;

use sp1_zkvm::lib::secp256k1::Secp256k1Point;
use sp1_zkvm::lib::utils::AffinePoint;

// Keep domain tags identical to PVUGC/src/ct.rs
const DEM_TAG_DOMAIN: &[u8] = b"PVUGC/DEM/tag";
const DEM_KEYSTREAM_DOMAIN: &[u8] = b"PVUGC/DEM/keystream";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackagePublic {
    /// Domain separation / versioning to prevent cross-protocol replay.
    pub profile: Vec<u8>,

    /// Statement-only delta base (G2) on BW6-761, encoded as raw affine coordinates:
    /// `delta_base = x_le_96 || y_le_96` (192 bytes total).
    pub delta_base: Vec<u8>,

    /// Armed delta `D_delta` (G2) on BW6-761, encoded as raw affine coordinates:
    /// `delta_arm = x_le_96 || y_le_96` (192 bytes total).
    pub delta_arm: Vec<u8>,

    /// Baked target in GT (BW6-761 TargetField), encoded as raw Fq6 tower limbs:
    /// `(c0.c0, c0.c1, c0.c2, c1.c0, c1.c1, c1.c2)` each as `Fq` little-endian 96 bytes
    /// (576 bytes total).
    pub r_baked: Vec<u8>,

    /// DEM metadata binding digest (32 bytes).
    pub ad_digest: [u8; 32],

    /// Ciphertext bytes and tag.
    pub ciphertext: Vec<u8>,
    pub tau: [u8; 32],

    /// Compressed secp256k1 adaptor commitment `T_i` (as included in `AD_core`).
    ///
    /// Expected format: SEC1 compressed encoding, 33 bytes, 0x02/0x03 prefix.
    pub t_i_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackageWitness {
    /// rho in BW6-761 scalar field, canonical bytes (Fr serialization).
    pub rho: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfInput {
    pub public: ArmingPackagePublic,
    pub witness: ArmingPackageWitness,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfOutput {
    /// SHA-256 over a canonical encoding of the public package.
    pub pkg_digest: [u8; 32],
}

fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize().into()
}

fn sha256_concat(parts: &[&[u8]]) -> [u8; 32] {
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

fn encode_public(pkg: &ArmingPackagePublic) -> Vec<u8> {
    // Deterministic byte encoding independent of serde/bincode versions.
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

const FQ_BYTES: usize = 96;
const G2_AFFINE_BYTES: usize = 2 * FQ_BYTES;
const FQ3_BYTES: usize = 3 * FQ_BYTES;
const FQ6_BYTES: usize = 6 * FQ_BYTES;

fn deserialize_fr(bytes: &[u8]) -> Bw6Fr {
    // rho is private witness input; canonical checks here are not a security bottleneck, but we
    // keep it consistent with the unchecked strategy for BW6 parsing.
    Bw6Fr::deserialize_compressed_unchecked(bytes).expect("Fr deserialize (unchecked)")
}

fn parse_fq_le_96(bytes: &[u8]) -> bw6_syscall::Fq {
    assert_eq!(bytes.len(), FQ_BYTES, "expected 96 bytes for BW6-761 Fq limb encoding");
    let mut words = [0u32; bw6_syscall::FQ_WORDS];
    for i in 0..bw6_syscall::FQ_WORDS {
        let j = i * 4;
        words[i] = u32::from_le_bytes(bytes[j..j + 4].try_into().unwrap());
    }
    bw6_syscall::Fq(words)
}

fn parse_g2_affine_xy(bytes: &[u8]) -> bw6_syscall::G2Jacobian {
    assert_eq!(bytes.len(), G2_AFFINE_BYTES, "delta must be 192 bytes (x||y, each 96 bytes LE)");
    let x = parse_fq_le_96(&bytes[0..FQ_BYTES]);
    let y = parse_fq_le_96(&bytes[FQ_BYTES..2 * FQ_BYTES]);
    bw6_syscall::G2Jacobian::from_affine(x, y)
}

fn parse_fq3(bytes: &[u8]) -> bw6_syscall::Fq3 {
    assert_eq!(bytes.len(), FQ3_BYTES, "expected 288 bytes for BW6-761 Fq3 limb encoding");
    bw6_syscall::Fq3 {
        c0: parse_fq_le_96(&bytes[0..FQ_BYTES]),
        c1: parse_fq_le_96(&bytes[FQ_BYTES..2 * FQ_BYTES]),
        c2: parse_fq_le_96(&bytes[2 * FQ_BYTES..3 * FQ_BYTES]),
    }
}

fn parse_fq6(bytes: &[u8]) -> bw6_syscall::Fq6 {
    assert_eq!(bytes.len(), FQ6_BYTES, "expected 576 bytes for BW6-761 Fq6 limb encoding");
    bw6_syscall::Fq6 {
        c0: parse_fq3(&bytes[0..FQ3_BYTES]),
        c1: parse_fq3(&bytes[FQ3_BYTES..2 * FQ3_BYTES]),
    }
}

fn fq6_exp_windowed(base: &bw6_syscall::Fq6, exp: <Bw6Fr as PrimeField>::BigInt) -> bw6_syscall::Fq6 {
    // Fixed-window left-to-right exponentiation. This is the same algorithmic shape as the
    // arkworks-backed `cyclotomic_exp_windowed`, but uses syscall-backed field ops.
    const W: usize = 5;
    if exp.is_zero() {
        return bw6_syscall::Fq6::one();
    }

    // Precompute odd powers: g^(1), g^(3), ..., g^(2^W - 1)
    let g = *base;
    let g2 = g.square();
    let mut table: Vec<bw6_syscall::Fq6> = Vec::with_capacity(1 << (W - 1));
    table.push(g);
    for i in 1..(1 << (W - 1)) {
        let next = table[i - 1].mul(&g2);
        table.push(next);
    }

    let bits_le = exp.to_bits_le();
    let mut i: isize = (bits_le.len() as isize) - 1;
    while i >= 0 && !bits_le[i as usize] {
        i -= 1;
    }
    if i < 0 {
        return bw6_syscall::Fq6::one();
    }

    let mut acc = bw6_syscall::Fq6::one();
    while i >= 0 {
        if !bits_le[i as usize] {
            acc = acc.square();
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
        debug_assert!(value & 1 == 1);
        debug_assert!(value < (1 << W));

        let win_len = (i - j + 1) as usize;
        for _ in 0..win_len {
            acc = acc.square();
        }
        acc = acc.mul(&table[value >> 1]);
        i = j - 1;
    }

    acc
}

fn g2_mul_windowed_syscall(
    base: &bw6_syscall::G2Jacobian,
    exp: <Bw6Fr as PrimeField>::BigInt,
) -> bw6_syscall::G2Jacobian {
    #[cfg(target_os = "zkvm")]
    {
        const W: usize = 5;
        if exp.is_zero() {
            return bw6_syscall::G2Jacobian::zero();
        }
        if base.is_zero() {
            return *base;
        }

        let base_aff = bw6_syscall::G2Affine::from_jacobian_assume_affine(base);

        // table[i] = (2*i+1) * P in affine coordinates, using BW6761_G2_ADD/DOUBLE syscalls.
        let mut p2 = base_aff;
        p2.double_in_place();
        let mut table: Vec<bw6_syscall::G2Affine> = Vec::with_capacity(1 << (W - 1));
        table.push(base_aff);
        for i in 1..(1 << (W - 1)) {
            let mut next = table[i - 1];
            next.add_assign(&p2);
            table.push(next);
        }

        let bits_le = exp.to_bits_le();
        let mut i: isize = (bits_le.len() as isize) - 1;
        while i >= 0 && !bits_le[i as usize] {
            i -= 1;
        }
        if i < 0 {
            return bw6_syscall::G2Jacobian::zero();
        }

        // `None` denotes point-at-infinity accumulator.
        let mut acc: Option<bw6_syscall::G2Affine> = None;
        while i >= 0 {
            if !bits_le[i as usize] {
                if let Some(a) = acc.as_mut() {
                    a.double_in_place();
                }
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
            debug_assert!(value & 1 == 1);
            debug_assert!(value < (1 << W));

            let win_len = (i - j + 1) as usize;
            for _ in 0..win_len {
                if let Some(a) = acc.as_mut() {
                    a.double_in_place();
                }
            }
            let addend = table[value >> 1];
            match acc.as_mut() {
                Some(a) => a.add_assign(&addend),
                None => acc = Some(addend),
            }
            i = j - 1;
        }

        return acc
            .map(|a| a.to_jacobian())
            .unwrap_or_else(bw6_syscall::G2Jacobian::zero);
    }

    #[cfg(not(target_os = "zkvm"))]
    {
    // Fixed-window left-to-right scalar multiplication on G2 (variable base).
    const W: usize = 5;
    if exp.is_zero() {
        return bw6_syscall::G2Jacobian::zero();
    }
    if base.is_zero() {
        return *base;
    }

    // table[i] = (2*i+1) * P
    let mut p2 = *base;
    p2.double_in_place();
    let mut table: Vec<bw6_syscall::G2Jacobian> = Vec::with_capacity(1 << (W - 1));
    table.push(*base);
    for i in 1..(1 << (W - 1)) {
        let mut next = table[i - 1];
        next.add_assign(&p2);
        table.push(next);
    }

    let bits_le = exp.to_bits_le();
    let mut i: isize = (bits_le.len() as isize) - 1;
    while i >= 0 && !bits_le[i as usize] {
        i -= 1;
    }
    if i < 0 {
        return bw6_syscall::G2Jacobian::zero();
    }

    let mut acc = bw6_syscall::G2Jacobian::zero();
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
        debug_assert!(value & 1 == 1);
        debug_assert!(value < (1 << W));

        let win_len = (i - j + 1) as usize;
        for _ in 0..win_len {
            acc.double_in_place();
        }
        acc.add_assign(&table[value >> 1]);
        i = j - 1;
    }

    acc
    }
}

fn compute_tau_sha256(k_bytes: &[u8], ad_digest: &[u8; 32], ct: &[u8]) -> [u8; 32] {
    // Mirrors PVUGC/src/ct.rs:
    // tau = SHA256("PVUGC/DEM/tag" || k_bytes || ad_digest || ciphertext)
    sha256_concat(&[DEM_TAG_DOMAIN, k_bytes, ad_digest, ct])
}

fn derive_keystream_sha256_32(k_bytes: &[u8], ad_digest: &[u8; 32]) -> [u8; 32] {
    // Mirrors `PVUGC/src/ct.rs` for the only case we need here (len=32):
    // keystream = SHA256("PVUGC/DEM/keystream" || k_bytes || ad_digest || counter_le(0))
    let counter_bytes = 0u32.to_le_bytes();
    sha256_concat(&[DEM_KEYSTREAM_DOMAIN, k_bytes, ad_digest, &counter_bytes])
}

fn secp_scalar_be_to_words_le(scalar_be: &[u8; 32]) -> [u32; 8] {
    // SP1 `AffinePoint::mul_assign` consumes bits from u32 words in LSB-first order.
    // Convert scalar from big-endian bytes to little-endian u32 words.
    let mut le = *scalar_be;
    le.reverse();
    let mut out = [0u32; 8];
    for (i, chunk) in le.chunks_exact(4).enumerate() {
        out[i] = u32::from_le_bytes(chunk.try_into().unwrap());
    }
    out
}

fn secp_point_to_sec1_compressed(point: &Secp256k1Point) -> [u8; 33] {
    // `to_le_bytes()` returns 64 bytes: x_le || y_le.
    let le = point.to_le_bytes();
    assert_eq!(le.len(), 64);
    let (x_le, y_le) = le.split_at(32);

    // SEC1 compression prefix is based on y parity (least significant bit).
    let y_is_odd = (y_le[0] & 1u8) == 1u8;

    // SEC1 uses big-endian x coordinate.
    let mut out = [0u8; 33];
    out[0] = if y_is_odd { 0x03 } else { 0x02 };
    for i in 0..32 {
        out[1 + i] = x_le[31 - i];
    }
    out
}

fn cycle_tracker_report_start(name: &str) {
    // IMPORTANT: SP1's executor parses cycle-tracker commands per *write syscall* on stdout (fd=1).
    // `println!` can be chunked into multiple writes, so we emit the full line with a single
    // `sys_write` to make the cycle tracker reliable.
    let mut s = String::new();
    s.push_str("cycle-tracker-report-start: ");
    s.push_str(name);
    s.push('\n');
    sp1_zkvm::syscalls::sys_write(1, s.as_ptr(), s.len());
}

fn cycle_tracker_report_end(name: &str) {
    let mut s = String::new();
    s.push_str("cycle-tracker-report-end: ");
    s.push_str(name);
    s.push('\n');
    sp1_zkvm::syscalls::sys_write(1, s.as_ptr(), s.len());
}

pub fn main() {
    // Single private input containing both public package and witness rho.
    let input = sp1_zkvm::io::read::<ArmingWfInput>();

    // Bind proof to the package by committing its digest.
    let encoded = encode_public(&input.public);
    let pkg_digest = sha256(&encoded);
    sp1_zkvm::io::commit(&ArmingWfOutput { pkg_digest });

    // --- Core well-formedness checks ---

    // Deserialize rho and forbid rho=0
    cycle_tracker_report_start("bw6_deser_rho");
    let rho = deserialize_fr(&input.witness.rho);
    assert!(!rho.is_zero(), "rho is zero");
    let rho_bigint = rho.into_bigint();
    cycle_tracker_report_end("bw6_deser_rho");

    // Deserialize delta bases/arms.
    cycle_tracker_report_start("bw6_deser_delta");
    let delta_base_j = parse_g2_affine_xy(&input.public.delta_base);
    let delta_arm_j = parse_g2_affine_xy(&input.public.delta_arm);
    cycle_tracker_report_end("bw6_deser_delta");
    // Outside SP1 must enforce on-curve + subgroup + non-identity. Here we minimally forbid the
    // all-zero coordinate encoding (common "identity/invalid" sentinel).
    assert!(
        !(delta_base_j.x.is_zero() && delta_base_j.y.is_zero()),
        "delta_base is identity"
    );
    // Symmetric defense-in-depth: outside-SP1 already rejects identity/invalid `delta_arm`, but
    // if someone ever runs "guest-only verification" in a harness, this cheap check avoids
    // accepting the common all-zero sentinel.
    assert!(
        !(delta_arm_j.x.is_zero() && delta_arm_j.y.is_zero()),
        "delta_arm is identity"
    );

    // Check delta arming correctness: this publicly binds rho to the published arms.
    //
    // Full per-column arm correctness (all D_j = rho*Y_j) must be enforced outside SP1 via PoCE.
    cycle_tracker_report_start("delta_arm_check");
    // Avoid arkworks big-int field arithmetic in the RV32 trace by doing G2 arithmetic over an
    // SP1-syscall-backed Fq representation.
    //
    // Math is identical: D_delta ?= rho * delta_base  <=>  (rho*delta_base - D_delta) == 0.
    let mut delta_diff = g2_mul_windowed_syscall(&delta_base_j, rho_bigint);
    delta_diff.sub_assign(&delta_arm_j);
    assert!(delta_diff.is_zero(), "mismatched delta arm");
    cycle_tracker_report_end("delta_arm_check");

    // Deserialize R_baked and compute K = R_baked^rho (inside ZK; K stays private).
    cycle_tracker_report_start("bw6_deser_r_baked");
    let r_baked_fq6 = parse_fq6(&input.public.r_baked);
    assert!(!r_baked_fq6.is_zero(), "R_baked is zero");
    assert!(!r_baked_fq6.is_one(), "R_baked is one");
    cycle_tracker_report_end("bw6_deser_r_baked");

    // Pairing outputs are in the cyclotomic subgroup. For BW6-761 Fp6, cyclotomic squaring is the
    // same as generic squaring (the main win is that inverse is conjugation), so we just run our
    // fixed-window exp with syscall-backed field multiplications.
    cycle_tracker_report_start("gt_pow");
    let k_fq6 = fq6_exp_windowed(&r_baked_fq6, rho_bigint);
    cycle_tracker_report_end("gt_pow");

    cycle_tracker_report_start("bw6_ser_k");
    let k_bytes = k_fq6.to_bytes_le_vec();
    cycle_tracker_report_end("bw6_ser_k");

    assert_eq!(
        input.public.t_i_bytes.len(),
        33,
        "t_i_bytes must be SEC1 compressed (33 bytes)"
    );

    // Recompute tag and compare
    cycle_tracker_report_start("dem_tag");
    let tau_prime = compute_tau_sha256(&k_bytes, &input.public.ad_digest, &input.public.ciphertext);
    assert_eq!(tau_prime, input.public.tau, "DEM tag mismatch (bricking)");
    cycle_tracker_report_end("dem_tag");

    // Plaintext well-formedness: ciphertext decrypts to the intended adaptor share scalar
    // committed by the public secp256k1 point `T_i` in AD_core.
    assert_eq!(
        input.public.ciphertext.len(),
        32,
        "ciphertext must be 32 bytes for adaptor scalar"
    );
    cycle_tracker_report_start("dem_decrypt");
    let ks = derive_keystream_sha256_32(&k_bytes, &input.public.ad_digest);
    let mut pt = [0u8; 32];
    for i in 0..32 {
        pt[i] = input.public.ciphertext[i] ^ ks[i];
    }
    cycle_tracker_report_end("dem_decrypt");

    // Check: T_i' = pt * G equals the published compressed point bytes.
    cycle_tracker_report_start("secp_mul");
    let scalar_words = secp_scalar_be_to_words_le(&pt);
    let mut p = Secp256k1Point::GENERATOR_T;
    p.mul_assign(&scalar_words);
    let t_prime = secp_point_to_sec1_compressed(&p);
    cycle_tracker_report_end("secp_mul");
    assert_eq!(
        &t_prime[..],
        input.public.t_i_bytes.as_slice(),
        "plaintext does not match adaptor commitment T_i"
    );
}

