use core::fmt;
use serde::{Deserialize, Serialize};

use pq_ccolo_wz17::Wz17GateArtifactV1;

/// Raw statement bytes that the tag binds to.
///
/// For Track-A, this should be a deterministic encoding of (shape_id, vk digest / program id,
/// and the public inputs) — i.e. values that uniquely define the statement whose witness is being checked.
pub type StatementBytes = Vec<u8>;

/// 32-byte statement hash (e.g. SHA-256 of `StatementBytes`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StatementHash32(pub [u8; 32]);

impl fmt::Debug for StatementHash32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StatementHash32({})", hex::encode(self.0))
    }
}

/// Per-armer domain separation id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArmerId(pub u32);

/// Human-readable shape id (domain separation across different oracle shapes/relations).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ShapeId(pub String);

/// CRT limb tag: (limbs mod moduli).
///
/// This matches the GPT Pro plan: compute `d` independent exact limbs in BFV/BGV,
/// then compare the limb vector against `alpha_limbs`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TagCrt {
    /// Plaintext moduli per limb (len = d).
    pub moduli: Vec<u64>,
    /// Limb values reduced mod corresponding modulus (len = d).
    pub limbs: Vec<u64>,
}

/// CRT limb alpha target.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlphaCrt {
    pub moduli: Vec<u64>,
    pub limbs: Vec<u64>,
}

/// Optional raw 256-bit value (debug only).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Tag256(pub [u8; 32]);

impl fmt::Debug for Tag256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tag256({})", hex::encode(self.0))
    }
}

/// Optional raw 256-bit alpha (debug only).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Alpha256(pub [u8; 32]);

impl fmt::Debug for Alpha256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Alpha256({})", hex::encode(self.0))
    }
}

/// Identifier for a particular lock artifact (debug/traceability only).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LockId(pub String);

/// v0 lock artifact descriptor.
///
/// This is *not* the final artifact format; it's the minimal binding info we know we need.
/// Actual encrypted payloads (e.g. HE ciphertexts / evaluation keys / key-switch hints) will be added
/// once the PQ plan is finalized.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LockArtifactV0 {
    /// Human-readable id for traceability.
    pub lock_id: LockId,

    /// Domain separation for the relation/shape.
    pub shape_id: ShapeId,

    /// Which armer this lock corresponds to (N-of-N).
    pub armer_id: ArmerId,

    /// Statement binding hash.
    pub statement_hash: StatementHash32,

    /// CRT moduli used for the tag limbs (len = d).
    pub moduli: Vec<u64>,

    /// Optional: alpha target in clear (dev/testing only).
    ///
    /// Production will keep alpha inside the gate (CCO/LO).
    pub alpha_clear: Option<AlphaCrt>,
}

/// v1 lock artifact descriptor (intended for the **real** CCO/LO gate path).
///
/// Unlike v0, this artifact is intended to keep `alpha` and `sigma` *inside* the gate object.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LockArtifactV1 {
    /// Human-readable id for traceability.
    pub lock_id: LockId,

    /// Domain separation for the relation/shape.
    pub shape_id: ShapeId,

    /// Which armer this lock corresponds to (N-of-N).
    pub armer_id: ArmerId,

    /// Statement binding hash.
    pub statement_hash: StatementHash32,

    /// CRT moduli used for the tag limbs (len = d).
    pub moduli: Vec<u64>,

    /// Public commitment to the released share (for auditing / accountability).
    ///
    /// Matches GPT‑Pro plan nomenclature: `c_i = H(sigma_i)`.
    pub sigma_commitment: [u8; 32],

    /// Opaque Wichs–Zirdelis style compute-and-compare gate.
    pub gate: Wz17GateArtifactV1,
}


