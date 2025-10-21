// src/error.rs

#[derive(Debug)]
pub enum Error {
    InvalidRho,
    NotInPrimeSubgroup,
    InvalidDelta,
    ColumnLengthMismatch,
    InvalidG1Limb,
    Mismatch, // keep for future comparisons if needed
}

pub type Result<T> = core::result::Result<T, Error>;

// Optional but nice: readable messages (so Display/anyhow prints make sense)
impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::InvalidRho => write!(f, "invalid rho (zero)"),
            Error::NotInPrimeSubgroup => write!(f, "point not in the prime subgroup"),
            Error::InvalidDelta => write!(f, "delta invalid (zero or not in subgroup)"),
            Error::ColumnLengthMismatch => write!(f, "mismatched column lengths: |X_B| != |Y^rho|"),
            Error::InvalidG1Limb => write!(f, "invalid G1 limb in commitments"),
            Error::Mismatch => write!(f, "mismatch"),
        }
    }
}

impl std::error::Error for Error {}
