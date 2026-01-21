//! Threshold LWE "share-lock" primitive (Architecture‑T scaffold).
//!
//! This crate provides the **locking** layer described in `PQ_WE_ARCHITECTURE_T.md`:
//! - an armer publishes noisy linear hints + AEAD ciphertexts of Shamir shares,
//! - anyone with the correct witness vector can derive enough AEAD keys to decrypt
//!   threshold-many shares and reconstruct the secret.
//!
//! Important:
//! - This is a **prototype scaffold** to exercise end-to-end wiring and test vectors.
//! - Security depends on concrete parameter choices (q, noise, dimension) and on
//!   the upstream DPP linearization producing a bounded integer witness vector.

pub mod shamir;
pub mod share_lock;

pub use shamir::{ShamirConfig, ShamirShare};
pub use share_lock::{
    derive_query_u64, derive_target_u32, statement_hash,
    ArmConfig, ArmKey, DecapConfig, LockArtifact, LockError,
    arm_lockset, decap_lockset,
};

