//! Minimal local test-artifacts crate for PVUGC.
//!
//! This avoids depending on SP1's upstream `test-artifacts` crate, which requires
//! the SP1 guest ("succinct") toolchain at build time.

/// Prebuilt SP1 guest ELF used by PVUGC tests.
pub const FIBONACCI_ELF: &[u8] = include_bytes!("../elf/fibonacci.elf");

/// Additional prebuilt SP1 guest ELFs (committed blobs) used by PVUGC tests.
pub const SSZ_WITHDRAWALS_ELF: &[u8] = include_bytes!("../elf/ssz-withdrawals.elf");
pub const TENDERMINT_ELF: &[u8] = include_bytes!("../elf/tendermint.elf");


