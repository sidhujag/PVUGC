//! Host-side arming well-formedness package acceptance checks.
//!
//! This module implements the **outside-SP1** checklist from the security spec:
//! - canonical parsing / length checks for the published package bytes
//! - on-curve + subgroup checks for BW6-761 G2 points (`delta_base`, `delta_arm`)
//! - GT (TargetField) r-torsion membership check for `r_baked` (rejects attacker-chosen garbage)
//! - binding check that the SP1 proof's committed `pkg_digest` matches the exact package bytes
//!
//! The SP1 guest intentionally uses fast limb parsing and does **not** enforce full group hygiene.
//! Every recipient/armer must run these checks before accepting a package.

use ark_bw6_761::{BW6_761, Fq, Fq3, Fq6};
use ark_ec::AffineRepr;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::{Field, One, PrimeField, Zero};
use sha2::{Digest, Sha256};

use crate::error::{Error, Result as PvugcResult};

pub const BW6_FQ_BYTES: usize = 96;
pub const BW6_G2_AFFINE_BYTES: usize = 2 * BW6_FQ_BYTES;
pub const BW6_FQ6_BYTES: usize = 6 * BW6_FQ_BYTES;

#[derive(Clone, Debug)]
pub struct ArmingWfPackagePublicBytes {
    pub profile: Vec<u8>,
    pub delta_base: Vec<u8>,
    pub delta_arm: Vec<u8>,
    pub r_baked: Vec<u8>,
    pub ad_digest: [u8; 32],
    pub ciphertext: Vec<u8>,
    pub tau: [u8; 32],
    pub t_i_bytes: Vec<u8>,
}

#[derive(Clone, Debug)]
pub struct AuditedArmingWfPackagePublic {
    pub pkg: ArmingWfPackagePublicBytes,
    pub delta_base: <BW6_761 as Pairing>::G2Affine,
    pub delta_arm: <BW6_761 as Pairing>::G2Affine,
    pub r_baked: PairingOutput<BW6_761>,
    pub pkg_digest: [u8; 32],
}

fn serialize_bytes_len_prefixed(out: &mut Vec<u8>, v: &[u8]) {
    let len_u32: u32 = v
        .len()
        .try_into()
        .expect("vector too large to length-prefix");
    out.extend_from_slice(&len_u32.to_le_bytes());
    out.extend_from_slice(v);
}

/// Must match `sp1-arming-wf/program/src/main.rs::encode_public`.
pub fn encode_public(pkg: &ArmingWfPackagePublicBytes) -> Vec<u8> {
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

pub fn compute_pkg_digest(pkg: &ArmingWfPackagePublicBytes) -> [u8; 32] {
    let encoded = encode_public(pkg);
    Sha256::digest(&encoded).into()
}

fn parse_fq_canonical_le_96(bytes: &[u8]) -> PvugcResult<Fq> {
    if bytes.len() != BW6_FQ_BYTES {
        return Err(Error::Crypto(format!(
            "invalid BW6 Fq length: expected {}, got {}",
            BW6_FQ_BYTES,
            bytes.len()
        )));
    }

    // BW6-761 Fq uses a 12-limb (u64) BigInt (768 bits).
    let mut limbs = [0u64; 12];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let j = i * 8;
        *limb = u64::from_le_bytes(bytes[j..j + 8].try_into().expect("slice"));
    }
    let bigint = ark_ff::BigInt::<12>::new(limbs);

    // Canonical parse: reject values >= modulus.
    Fq::from_bigint(bigint).ok_or_else(|| Error::Crypto("non-canonical BW6 Fq element".to_string()))
}

fn parse_g2_affine_xy_canonical(bytes: &[u8]) -> PvugcResult<<BW6_761 as Pairing>::G2Affine> {
    if bytes.len() != BW6_G2_AFFINE_BYTES {
        return Err(Error::Crypto(format!(
            "invalid delta length: expected {}, got {}",
            BW6_G2_AFFINE_BYTES,
            bytes.len()
        )));
    }

    let x = parse_fq_canonical_le_96(&bytes[0..BW6_FQ_BYTES])?;
    let y = parse_fq_canonical_le_96(&bytes[BW6_FQ_BYTES..2 * BW6_FQ_BYTES])?;

    let p = <BW6_761 as Pairing>::G2Affine::new(x, y);
    if !p.is_on_curve() {
        return Err(Error::Crypto("BW6 G2 point not on curve".to_string()));
    }
    if !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err(Error::InvalidSubgroup);
    }
    Ok(p)
}

fn parse_fq3(bytes: &[u8]) -> PvugcResult<Fq3> {
    if bytes.len() != 3 * BW6_FQ_BYTES {
        return Err(Error::Crypto(format!(
            "invalid BW6 Fq3 length: expected {}, got {}",
            3 * BW6_FQ_BYTES,
            bytes.len()
        )));
    }
    Ok(Fq3::new(
        parse_fq_canonical_le_96(&bytes[0..BW6_FQ_BYTES])?,
        parse_fq_canonical_le_96(&bytes[BW6_FQ_BYTES..2 * BW6_FQ_BYTES])?,
        parse_fq_canonical_le_96(&bytes[2 * BW6_FQ_BYTES..3 * BW6_FQ_BYTES])?,
    ))
}

fn parse_fq6(bytes: &[u8]) -> PvugcResult<Fq6> {
    if bytes.len() != BW6_FQ6_BYTES {
        return Err(Error::Crypto(format!(
            "invalid BW6 Fq6 length: expected {}, got {}",
            BW6_FQ6_BYTES,
            bytes.len()
        )));
    }
    let c0 = parse_fq3(&bytes[0..3 * BW6_FQ_BYTES])?;
    let c1 = parse_fq3(&bytes[3 * BW6_FQ_BYTES..6 * BW6_FQ_BYTES])?;
    Ok(Fq6::new(c0, c1))
}

fn check_gt_r_torsion(r_baked: &Fq6) -> PvugcResult<()> {
    // Ensure r_baked is in the r-torsion subgroup:
    // - reject identity (1)
    // - check r_baked^r == 1 where r is the scalar field modulus (prime)
    type Fr = <BW6_761 as Pairing>::ScalarField;
    let r = <Fr as PrimeField>::MODULUS;
    let one = Fq6::one();

    if r_baked.is_zero() {
        return Err(Error::Crypto("R_baked is zero".to_string()));
    }
    if *r_baked == one {
        return Err(Error::DegenerateTarget);
    }

    let check = r_baked.pow(r);
    if check != one {
        return Err(Error::Crypto("R_baked not in r-torsion subgroup".to_string()));
    }
    Ok(())
}

/// Perform outside-SP1 acceptance checks for the arming-wf public package.
///
/// This should be called by **every** recipient before accepting an arming package.
pub fn audit_public_package(pkg: ArmingWfPackagePublicBytes) -> PvugcResult<AuditedArmingWfPackagePublic> {
    // Length / format checks (must be done on raw bytes before using unchecked guest parsing).
    if pkg.ciphertext.len() != 32 {
        return Err(Error::Crypto(format!(
            "ciphertext must be 32 bytes, got {}",
            pkg.ciphertext.len()
        )));
    }
    if pkg.t_i_bytes.len() != 33 {
        return Err(Error::Crypto(format!(
            "t_i_bytes must be 33 bytes (SEC1 compressed), got {}",
            pkg.t_i_bytes.len()
        )));
    }
    if !matches!(pkg.t_i_bytes[0], 0x02 | 0x03) {
        return Err(Error::Crypto("t_i_bytes must have SEC1 compressed prefix 0x02/0x03".to_string()));
    }

    // Parse + validate G2 points.
    let delta_base = parse_g2_affine_xy_canonical(&pkg.delta_base)?;
    let delta_arm = parse_g2_affine_xy_canonical(&pkg.delta_arm)?;

    if delta_base.is_zero() {
        return Err(Error::ZeroDelta);
    }
    if delta_arm.is_zero() {
        return Err(Error::Crypto("delta_arm is identity".to_string()));
    }

    // Parse + validate r_baked.
    let r_baked_fq6 = parse_fq6(&pkg.r_baked)?;
    check_gt_r_torsion(&r_baked_fq6)?;
    let r_baked = PairingOutput::<BW6_761>(r_baked_fq6);

    let pkg_digest = compute_pkg_digest(&pkg);

    Ok(AuditedArmingWfPackagePublic { pkg, delta_base, delta_arm, r_baked, pkg_digest })
}

/// Check the SP1 proof's committed `pkg_digest` matches the exact received package bytes.
pub fn check_sp1_committed_pkg_digest(
    audited: &AuditedArmingWfPackagePublic,
    committed_pkg_digest: &[u8; 32],
) -> PvugcResult<()> {
    if &audited.pkg_digest != committed_pkg_digest {
        return Err(Error::Crypto("SP1 pkg_digest does not match received package bytes".to_string()));
    }
    Ok(())
}

/// Convenience wrapper: audit package bytes and check SP1 digest binding in one call.
pub fn accept_package_with_committed_digest(
    pkg: ArmingWfPackagePublicBytes,
    committed_pkg_digest: &[u8; 32],
) -> PvugcResult<AuditedArmingWfPackagePublic> {
    let audited = audit_public_package(pkg)?;
    check_sp1_committed_pkg_digest(&audited, committed_pkg_digest)?;
    Ok(audited)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_ec::PrimeGroup;
    use ark_ff::BigInteger;
    use ark_ff::UniformRand;
    use ark_std::rand::SeedableRng;

    #[test]
    fn audit_accepts_well_formed_package_bytes() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(20260224);

        // Random nonzero delta_base and corresponding delta_arm.
        let delta_base = (<BW6_761 as Pairing>::G2::generator() * <BW6_761 as Pairing>::ScalarField::rand(&mut rng))
            .into_affine();
        assert!(!delta_base.is_zero());

        let rho = <BW6_761 as Pairing>::ScalarField::rand(&mut rng);
        let delta_arm = (delta_base.into_group() * rho).into_affine();
        assert!(!delta_arm.is_zero());

        // r_baked: pairing output is in the correct subgroup.
        let r_baked = BW6_761::pairing(<BW6_761 as Pairing>::G1::generator(), <BW6_761 as Pairing>::G2::generator()).0;
        assert!(!r_baked.is_zero());
        assert_ne!(r_baked, Fq6::one());

        // Encode delta_base/delta_arm as x_le_96 || y_le_96.
        let fq_to_le_96 = |x: &Fq| -> Vec<u8> {
            let mut out = vec![0u8; BW6_FQ_BYTES];
            let le = x.into_bigint().to_bytes_le();
            out[..le.len()].copy_from_slice(&le);
            out
        };
        let g2_to_xy = |p: &<BW6_761 as Pairing>::G2Affine| -> Vec<u8> {
            let mut out = Vec::with_capacity(BW6_G2_AFFINE_BYTES);
            out.extend_from_slice(&fq_to_le_96(&p.x));
            out.extend_from_slice(&fq_to_le_96(&p.y));
            out
        };
        let gt_to_fq6 = |x: &Fq6| -> Vec<u8> {
            let mut out = Vec::with_capacity(BW6_FQ6_BYTES);
            out.extend_from_slice(&fq_to_le_96(&x.c0.c0));
            out.extend_from_slice(&fq_to_le_96(&x.c0.c1));
            out.extend_from_slice(&fq_to_le_96(&x.c0.c2));
            out.extend_from_slice(&fq_to_le_96(&x.c1.c0));
            out.extend_from_slice(&fq_to_le_96(&x.c1.c1));
            out.extend_from_slice(&fq_to_le_96(&x.c1.c2));
            out
        };

        let pkg = ArmingWfPackagePublicBytes {
            profile: b"PVUGC/test/profile/v1".to_vec(),
            delta_base: g2_to_xy(&delta_base),
            delta_arm: g2_to_xy(&delta_arm),
            r_baked: gt_to_fq6(&r_baked),
            ad_digest: [7u8; 32],
            ciphertext: [9u8; 32].to_vec(),
            tau: [11u8; 32],
            t_i_bytes: {
                // Just enforce format here; correctness is checked inside the SP1 guest.
                let mut t = vec![0u8; 33];
                t[0] = 0x02;
                t
            },
        };

        let audited = audit_public_package(pkg).expect("audit should accept");
        assert_eq!(audited.pkg_digest, compute_pkg_digest(&audited.pkg));
    }
}

