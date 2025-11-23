//! Error types for PVUGC library

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("input not in prime subgroup")]
    InvalidSubgroup,
    #[error("delta must be non-zero")]
    ZeroDelta,
    #[error("rho must be non-zero")]
    ZeroRho,
    #[error("mismatched vector sizes")]
    MismatchedSizes,
    #[error("invalid commitment element")]
    InvalidCommitment,
    #[error("cryptographic error: {0}")]
    Crypto(String),
    #[error("public input length mismatch: expected {expected}, got {actual}")]
    PublicInputLength { expected: usize, actual: usize },
    #[error("instance commitment IC(x) is zero (security-critical: enables partition of unity attack)")]
    ZeroInstanceCommitment,
    #[error("target R is degenerate (zero or one) - invalid statement")]
    DegenerateTarget,
    #[error("witness isolation hints missing or wrong length")]
    InvalidWitnessIsolationHints,
    #[error("witness columns touch public rows; refuse to arm")]
    UnsafeWitnessColumns,
    #[error("public residual lies in armed span; refuse to arm this statement")]
    UnsafePublicResidual,
}

pub type Result<T> = core::result::Result<T, Error>;
