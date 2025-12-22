//! gnark to arkworks Groth16 Proof Deserializer
//!
//! This module deserializes Groth16 proofs from gnark's binary format
//! into arkworks types for BLS12-377.
//!
//! This module deserializes **gnark's `WriteRawTo` (uncompressed) encoding** for Groth16
//! proofs and verifying keys into arkworks types for BLS12-377.
//!
//! Important: gnark does **not** serialize Groth16 proofs as a plain `A||B||C` tuple.
//! For BLS12-377, gnark's `(*Proof).WriteRawTo` encodes:
//! - `Ar` (G1Affine, uncompressed)
//! - `Bs` (G2Affine, uncompressed)
//! - `Krs` (G1Affine, uncompressed)
//! - plus optional commitment-related fields (not used by SP1).
//!
//! gnark-crypto uses IETF/ZCash-style flags in the MSBs of the first byte; for
//! **uncompressed** points we must clear those flag bits before interpreting X.

use ark_bls12_377::{Bls12_377, Fq, Fq2, G1Affine, G2Affine, Fr as Fr377};
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Proof, VerifyingKey};
use ark_serialize::CanonicalDeserialize;
use core::str::FromStr;

use super::Sp1BridgeError;

/// Decode hex string to bytes (no external dependency)
fn hex_decode(hex: &str) -> Result<Vec<u8>, Sp1BridgeError> {
    // Remove 0x prefix if present
    let hex = hex.strip_prefix("0x").unwrap_or(hex);
    
    if hex.len() % 2 != 0 {
        return Err(Sp1BridgeError::DeserializationError("Odd hex length".to_string()));
    }
    
    (0..hex.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&hex[i..i + 2], 16)
                .map_err(|_| Sp1BridgeError::DeserializationError(format!("Invalid hex at {}", i)))
        })
        .collect()
}

/// Parse SP1's hex-encoded proof string into raw bytes
pub fn decode_sp1_proof_hex(hex_proof: &str) -> Result<Vec<u8>, Sp1BridgeError> {
    hex_decode(hex_proof)
}

/// Parse SP1's hex-encoded public input into Fr377
pub fn decode_sp1_public_input(hex_input: &str) -> Result<Fr377, Sp1BridgeError> {
    let s = hex_input.trim();

    // SP1 (gnark-ffi) public inputs are provided as *strings* that gnark parses as big integers.
    // In this fork, they are emitted as decimal (BigUint::to_string()).
    //
    // However, some callers may provide `0x`-prefixed hex. Support both:
    // - Decimal: "123456..."
    // - Hex:     "0x12ab..."
    if let Some(hex) = s.strip_prefix("0x") {
        let bytes = hex_decode(hex)?;
        Ok(Fr377::from_be_bytes_mod_order(&bytes))
    } else {
        Fr377::from_str(s).map_err(|_| {
            Sp1BridgeError::DeserializationError(format!(
                "Invalid SP1 public input string (expected decimal or 0x-hex): {s}"
            ))
        })
    }
}

/// Size constants for BLS12-377 (gnark-crypto raw encoding)
pub const G1_RAW_SIZE: usize = 96;  // 48 * 2
pub const G2_RAW_SIZE: usize = 192; // 48 * 4 (Fp2 x,y)

/// gnark-crypto point encoding flags (top 3 bits of the first byte).
const GNARK_MASK: u8 = 0b1110_0000;
const GNARK_UNCOMPRESSED_INFINITY: u8 = 0b0100_0000; // 0b010 << 5

#[inline]
fn clear_gnark_flags(b0: u8) -> u8 {
    b0 & !GNARK_MASK
}

fn parse_fq_be_48(bytes48: &[u8]) -> Result<Fq, Sp1BridgeError> {
    if bytes48.len() != 48 {
        return Err(Sp1BridgeError::DeserializationError(format!(
            "Fq must be 48 bytes, got {}",
            bytes48.len()
        )));
    }
    // Interpret as a big-endian integer; enforce canonical encoding (no reduction).
    let fe = Fq::from_be_bytes_mod_order(bytes48);
    let canon = fe.into_bigint().to_bytes_be();
    let mut canon48 = [0u8; 48];
    if canon.len() > 48 {
        return Err(Sp1BridgeError::DeserializationError(
            "Invalid Fq encoding (too large)".to_string(),
        ));
    }
    canon48[48 - canon.len()..].copy_from_slice(&canon);
    if canon48 != bytes48 {
        return Err(Sp1BridgeError::DeserializationError(
            "Non-canonical Fq encoding".to_string(),
        ));
    }
    Ok(fe)
}

fn parse_g1_affine_gnark_raw(bytes: &[u8]) -> Result<G1Affine, Sp1BridgeError> {
    if bytes.len() < G1_RAW_SIZE {
        return Err(Sp1BridgeError::InvalidProofFormat(format!(
            "G1 raw should be {} bytes, got {}",
            G1_RAW_SIZE,
            bytes.len()
        )));
    }
    let flag = bytes[0] & GNARK_MASK;
    if flag == GNARK_UNCOMPRESSED_INFINITY {
        if bytes[0] & !GNARK_MASK != 0 || bytes[1..G1_RAW_SIZE].iter().any(|&b| b != 0) {
            return Err(Sp1BridgeError::InvalidProofFormat(
                "Invalid G1 infinity encoding".to_string(),
            ));
        }
        return Ok(G1Affine::identity());
    }
    if flag != 0 {
        return Err(Sp1BridgeError::InvalidProofFormat(
            "Expected uncompressed G1 encoding (WriteRawTo)".to_string(),
        ));
    }
    
    let mut x_bytes = bytes[0..48].to_vec();
    x_bytes[0] = clear_gnark_flags(x_bytes[0]);
    let y_bytes = &bytes[48..96];

    let x = parse_fq_be_48(&x_bytes)?;
    let y = parse_fq_be_48(y_bytes)?;
    let p = G1Affine::new(x, y);
    if !p.is_on_curve() {
        return Err(Sp1BridgeError::InvalidProofFormat("G1 not on curve".to_string()));
    }
    // Subgroup check is required when bypassing arkworks' canonical deserialization.
    if !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err(Sp1BridgeError::InvalidProofFormat(
            "G1 not in correct subgroup".to_string(),
        ));
    }
    Ok(p)
}

fn parse_g2_affine_gnark_raw(bytes: &[u8]) -> Result<G2Affine, Sp1BridgeError> {
    if bytes.len() < G2_RAW_SIZE {
        return Err(Sp1BridgeError::InvalidProofFormat(format!(
            "G2 raw should be {} bytes, got {}",
            G2_RAW_SIZE,
            bytes.len()
        )));
    }
    let flag = bytes[0] & GNARK_MASK;
    if flag == GNARK_UNCOMPRESSED_INFINITY {
        if bytes[0] & !GNARK_MASK != 0 || bytes[1..G2_RAW_SIZE].iter().any(|&b| b != 0) {
        return Err(Sp1BridgeError::InvalidProofFormat(
                "Invalid G2 infinity encoding".to_string(),
        ));
    }
        return Ok(G2Affine::identity());
}
    if flag != 0 {
        return Err(Sp1BridgeError::InvalidProofFormat(
            "Expected uncompressed G2 encoding (WriteRawTo)".to_string(),
        ));
    }

    // gnark-crypto RawBytes order for Fq2: A1||A0, with flags in the MSBs of A1[0].
    // Total order: X.A1 | X.A0 | Y.A1 | Y.A0
    let mut x_a1 = bytes[0..48].to_vec();
    x_a1[0] = clear_gnark_flags(x_a1[0]);
    let x_a0 = &bytes[48..96];
    let y_a1 = &bytes[96..144];
    let y_a0 = &bytes[144..192];

    let x_c1 = parse_fq_be_48(&x_a1)?;
    let x_c0 = parse_fq_be_48(x_a0)?;
    let y_c1 = parse_fq_be_48(y_a1)?;
    let y_c0 = parse_fq_be_48(y_a0)?;
    
    let x = Fq2::new(x_c0, x_c1);
    let y = Fq2::new(y_c0, y_c1);
    let p = G2Affine::new(x, y);
    if !p.is_on_curve() {
        return Err(Sp1BridgeError::InvalidProofFormat("G2 not on curve".to_string()));
    }
    // Subgroup check is required when bypassing arkworks' canonical deserialization.
    if !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err(Sp1BridgeError::InvalidProofFormat(
            "G2 not in correct subgroup".to_string(),
        ));
    }
    Ok(p)
}

/// Wrapper type for SP1's Groth16 proof over BLS12-377
pub type Sp1Groth16Proof = Proof<Bls12_377>;

/// Wrapper type for SP1's verification key over BLS12-377
pub type Sp1VerifyingKey = VerifyingKey<Bls12_377>;

/// Parse a gnark Groth16 proof (gnark `WriteRawTo` format) into arkworks types.
///
/// # Arguments
/// * `raw_proof` - The raw proof bytes from gnark `(*Proof).WriteRawTo(...)`
///
/// # Returns
/// * `Proof<Bls12_377>` - The arkworks proof
pub fn parse_gnark_proof_bls12_377(raw_proof: &[u8]) -> Result<Sp1Groth16Proof, Sp1BridgeError> {
    // gnark WriteRawTo encodes Ar (G1 raw) | Bs (G2 raw) | Krs (G1 raw) | ...
    let min = G1_RAW_SIZE + G2_RAW_SIZE + G1_RAW_SIZE;
    if raw_proof.len() < min {
        return Err(Sp1BridgeError::InvalidProofFormat(format!(
            "Proof too short: need at least {} bytes, got {}",
            min,
            raw_proof.len()
        )));
    }

    let a = parse_g1_affine_gnark_raw(&raw_proof[0..G1_RAW_SIZE])?;
    let b = parse_g2_affine_gnark_raw(&raw_proof[G1_RAW_SIZE..G1_RAW_SIZE + G2_RAW_SIZE])?;
    let c = parse_g1_affine_gnark_raw(
        &raw_proof[G1_RAW_SIZE + G2_RAW_SIZE..G1_RAW_SIZE + G2_RAW_SIZE + G1_RAW_SIZE],
    )?;
    
    Ok(Proof { a, b, c })
}

/// Parse a gnark verification key from gnark `WriteRawTo` format (uncompressed points).
///
/// gnark `VerifyingKey.writeTo(raw=true)` ordering:
/// [α]1,[β]1,[β]2,[γ]2,[δ]1,[δ]2, len(K), [K]1, publicCommitted, nbCommitments, commitmentKeys...
///
/// PVUGC only needs: alpha_g1, beta_g2, gamma_g2, delta_g2, and K (IC points).
pub fn parse_gnark_vk_bls12_377(raw_vk: &[u8]) -> Result<Sp1VerifyingKey, Sp1BridgeError> {
    // Minimum prefix: alpha(96) + beta_g1(96) + beta_g2(192) + gamma_g2(192) + delta_g1(96) + delta_g2(192) + len(K)(4) + at least 1 K (96)
    let min = 96 + 96 + 192 + 192 + 96 + 192 + 4 + 96;
    if raw_vk.len() < min {
        return Err(Sp1BridgeError::InvalidVkFormat(format!(
            "VK too short: {} bytes, need at least {}",
            raw_vk.len(),
            min
        )));
    }

    let mut offset = 0usize;

    let alpha_g1 = parse_g1_affine_gnark_raw(&raw_vk[offset..offset + G1_RAW_SIZE])?;
    offset += G1_RAW_SIZE;

    // Skip G1.Beta (gnark includes it; arkworks VK doesn't store it)
    offset += G1_RAW_SIZE;

    let beta_g2 = parse_g2_affine_gnark_raw(&raw_vk[offset..offset + G2_RAW_SIZE])?;
    offset += G2_RAW_SIZE;

    let gamma_g2 = parse_g2_affine_gnark_raw(&raw_vk[offset..offset + G2_RAW_SIZE])?;
    offset += G2_RAW_SIZE;

    // Skip G1.Delta (gnark includes it; arkworks VK doesn't store it)
    offset += G1_RAW_SIZE;

    let delta_g2 = parse_g2_affine_gnark_raw(&raw_vk[offset..offset + G2_RAW_SIZE])?;
    offset += G2_RAW_SIZE;

    if offset + 4 > raw_vk.len() {
        return Err(Sp1BridgeError::InvalidVkFormat("VK missing K length".to_string()));
    }
    let k_len = u32::from_be_bytes(raw_vk[offset..offset + 4].try_into().unwrap()) as usize;
    offset += 4;

    if offset + k_len * G1_RAW_SIZE > raw_vk.len() {
        return Err(Sp1BridgeError::InvalidVkFormat(
            "VK truncated in K points".to_string(),
        ));
    }

    let mut gamma_abc_g1 = Vec::with_capacity(k_len);
    for i in 0..k_len {
        let start = offset + i * G1_RAW_SIZE;
        let end = start + G1_RAW_SIZE;
        gamma_abc_g1.push(parse_g1_affine_gnark_raw(&raw_vk[start..end])?);
    }
    offset += k_len * G1_RAW_SIZE;

    // Remaining fields: publicCommitted ([][]uint64), nbCommitments (uint32), commitmentKeys...
    // SP1's Groth16 wrapper should not use commitments; we accept and ignore publicCommitted but enforce nbCommitments==0.
    if offset + 4 > raw_vk.len() {
        return Err(Sp1BridgeError::InvalidVkFormat("VK missing publicCommitted".to_string()));
    }
    let outer_len = u32::from_be_bytes(raw_vk[offset..offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    for _ in 0..outer_len {
        if offset + 4 > raw_vk.len() {
            return Err(Sp1BridgeError::InvalidVkFormat(
                "VK truncated in publicCommitted".to_string(),
            ));
        }
        let inner_len = u32::from_be_bytes(raw_vk[offset..offset + 4].try_into().unwrap()) as usize;
        offset += 4;
        let bytes = inner_len
            .checked_mul(8)
            .ok_or_else(|| Sp1BridgeError::InvalidVkFormat("publicCommitted too large".to_string()))?;
        if offset + bytes > raw_vk.len() {
            return Err(Sp1BridgeError::InvalidVkFormat(
                "VK truncated in publicCommitted inner".to_string(),
            ));
        }
        offset += bytes;
    }

    if offset + 4 > raw_vk.len() {
        return Err(Sp1BridgeError::InvalidVkFormat("VK missing nbCommitments".to_string()));
    }
    let nb_commitments = u32::from_be_bytes(raw_vk[offset..offset + 4].try_into().unwrap());
    if nb_commitments != 0 {
        return Err(Sp1BridgeError::InvalidVkFormat(
            "Commitment keys not supported in PVUGC bridge (expected nbCommitments=0)".to_string(),
        ));
    }

    Ok(VerifyingKey { alpha_g1, beta_g2, gamma_g2, delta_g2, gamma_abc_g1 })
}

/// Alternative: Parse VK from arkworks-native format
/// Use this if the SP1 fork exports VK in arkworks format
pub fn parse_arkworks_vk_bls12_377(raw_vk: &[u8]) -> Result<Sp1VerifyingKey, Sp1BridgeError> {
    VerifyingKey::deserialize_compressed(raw_vk)
        .map_err(|e| Sp1BridgeError::InvalidVkFormat(format!("Failed to deserialize VK: {}", e)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::BigInteger;
    use ark_std::{test_rng, UniformRand};
    
    #[test]
    fn test_parse_g1_raw_smoke() {
        let mut rng = test_rng();
        let p = G1Affine::rand(&mut rng);

        // Recreate gnark-crypto RawBytes format: X (48 BE, top 3 bits masked), then Y.
        let mut out = [0u8; G1_RAW_SIZE];
        let x = p.x.into_bigint().to_bytes_be();
        let y = p.y.into_bigint().to_bytes_be();
        if x.len() > 48 || y.len() > 48 {
            panic!("unexpected field byte length");
        }
        out[48 - x.len()..48].copy_from_slice(&x);
        out[96 - y.len()..96].copy_from_slice(&y);
        out[0] &= !GNARK_MASK; // mimic mUncompressed

        let parsed = parse_g1_affine_gnark_raw(&out).unwrap();
        assert_eq!(parsed, p);
    }

    #[test]
    fn test_decode_sp1_public_input_decimal() {
        // SP1 gnark-ffi witness emits public inputs as decimal strings (BigUint::to_string()).
        let s = "1234567890123456789012345678901234567890";
        let decoded = decode_sp1_public_input(s).unwrap();
        let expected = Fr377::from_str(s).unwrap();
        assert_eq!(decoded, expected);
    }

    #[test]
    fn test_decode_sp1_public_input_hex_prefixed() {
        // Accept 0x-prefixed hex as a convenience.
        let decoded = decode_sp1_public_input("0x01").unwrap();
        let expected = Fr377::from_be_bytes_mod_order(&[1u8]);
        assert_eq!(decoded, expected);
    }
}

