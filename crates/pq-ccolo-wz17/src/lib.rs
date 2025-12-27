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
