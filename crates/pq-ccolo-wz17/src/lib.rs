//! Wichs–Zirdelis (ePrint 2017/276, FOCS 2017) compute-and-compare / lockable obfuscation scaffolding.
//!
//! This crate is intentionally **not** a full implementation yet. It provides:
//! - stable artifact boundaries (serialization types)
//! - a backend API that PVUGC can call from `pvugc::pq_we::PqLockBackend`
//!
//! Cryptographic implementation notes live in:
//! - `docs/CCOLO_WICHZIRDELIS_2017_NOTES.md`
//!
//! WARNING: Do not use this crate for security until the construction is fully implemented and reviewed.

use serde::{Deserialize, Serialize};
use std::convert::TryInto;

/// Gate boundary input: a set of extracted LWE samples (one per limb), plus decode semantics.
///
/// This is *not* the obfuscated gate itself. It is the stable “bridge output” that the real gate will consume.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GateInputV0 {
    pub meta: GateMetaV0,
    /// LWE samples (len == d_limbs). Each sample is coefficient-0 extraction after ModReduce-to-one-tower.
    pub samples: Vec<LweSampleU64V0>,
}

/// Metadata describing how to interpret the extracted LWE samples.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GateMetaV0 {
    /// BFV plaintext modulus used by the OpenFHE evaluator (e.g. 65537).
    pub t_bfv: u64,
    /// Gate message modulus (byte limbs plan: 256).
    pub t_gate: u64,
    /// Limb count d.
    pub d_limbs: usize,
    /// Statement hash bound into the stream/tag computation (for traceability).
    pub statement_hash_hex: String,
    /// Shape id / domain separation string (for traceability).
    pub shape_id: String,
}

/// Minimal representation of an extracted LWE sample at the bridge boundary.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LweSampleU64V0 {
    /// Modulus q (single tower after ModReduce).
    pub q: u64,
    /// Mask vector a (len = N).
    pub a: Vec<u64>,
    /// Body b.
    pub b: u64,
}

/// Placeholder loader for `.lwe0` dumps emitted by PVUGC OpenFHE decap tooling.
///
/// Format matches `pq_fhe_openfhe::LweSampleU64::write_to_file`:
/// - magic: b"LWE0"
/// - q: u64 LE
/// - n: u32 LE
/// - b: u64 LE
/// - a[0..n): u64 LE
pub fn read_lwe0(bytes: &[u8]) -> Result<LweSampleU64V0, Wz17Error> {
    if bytes.len() < 4 + 8 + 4 + 8 {
        return Err(Wz17Error::NotImplemented);
    }
    if &bytes[0..4] != b"LWE0" {
        return Err(Wz17Error::NotImplemented);
    }
    let mut off = 4;
    let q = u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap());
    off += 8;
    let n = u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap()) as usize;
    off += 4;
    let b = u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap());
    off += 8;
    let need = off + n * 8;
    if bytes.len() != need {
        return Err(Wz17Error::NotImplemented);
    }
    let mut a = Vec::with_capacity(n);
    for i in 0..n {
        let x = u64::from_le_bytes(bytes[off + i * 8..off + (i + 1) * 8].try_into().unwrap());
        a.push(x);
    }
    Ok(LweSampleU64V0 { q, a, b })
}

/// Serialized “real gate” artifact placeholder.
///
/// Design intent: this is the thing that replaces v0 `alpha_clear + decrypt+compare`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Wz17GateArtifactV1 {
    /// Domain separation / versioning for decoding.
    pub scheme_id: String,
    /// Opaque bytes for the obfuscated program / lock material.
    ///
    /// Format is construction-dependent and will be specified once we pick the exact instantiation path.
    pub gate_bytes: Vec<u8>,
}

#[derive(thiserror::Error, Debug)]
pub enum Wz17Error {
    #[error("WZ17 gate is not implemented yet")]
    NotImplemented,
}

/// Decapsulate a key share from a ciphertext-tag input.
///
/// This API will evolve once we commit to the concrete Wichs–Zirdelis instantiation.
pub fn decap_v1(
    _gate: &Wz17GateArtifactV1,
    _tag_ciphertext_bytes: &[u8],
) -> Result<Option<Vec<u8>>, Wz17Error> {
    Err(Wz17Error::NotImplemented)
}
