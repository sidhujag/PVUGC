//! Post-quantum Witness Encryption / Lockable Obfuscation (Track-A) scaffolding.
//!
//! This module is intentionally *interface-only* for now:
//! - defines artifact boundaries and types (tag/alpha/statement binding)
//! - does NOT commit to any specific PQ construction or HE backend yet
//! - does NOT introduce heavy dependencies
//!
//! Once the concrete plan is finalized, we will implement:
//! - arming-time artifact generation (per-shape blob + per-statement lock)
//! - decap-time evaluation from a streaming tag (SP1 side) to a key share

mod types;
mod weights;
mod blob;

pub use types::{
    Alpha256, AlphaCrt, ArmerId, LockArtifactV0, LockArtifactV1, LockId, ShapeId, StatementBytes,
    StatementHash32, Tag256, TagCrt,
};
pub use weights::{derive_weights_matrix, derive_weights_matrix_with_kind, WeightsKind, WeightsMatrix};
pub use blob::{rotations_powers_of_two, OpenFheLimbFilesV0, OpenFheManifestV0, ShapeBlobManifestV0};

/// High-level interface for a PQ lock backend.
///
/// Design intent:
/// - Input is *public* and minimal (statement binding + computed `Tag256`)
/// - Output is a key share iff unlock condition holds (internally enforced by the backend)
///
/// Concrete backends might be WZ17-style CCO+FHE, something lighter, or a v0 engineering bridge.
pub trait PqLockBackend {
    type KeyShare;
    type Error;

    /// Attempt to decapsulate (derive) the key share from a computed tag.
    ///
    /// Implementations must ensure:
    /// - Returns `Ok(Some(_))` iff `tag == alpha` under the lock's interpretation.
    /// - Returns `Ok(None)` on mismatch (no side-channel-y partial info).
    fn decap(&self, lock: &LockArtifactV0, tag: &TagCrt) -> Result<Option<Self::KeyShare>, Self::Error>;
}


