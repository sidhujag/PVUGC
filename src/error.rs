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
}

pub type Result<T> = core::result::Result<T, Error>;


