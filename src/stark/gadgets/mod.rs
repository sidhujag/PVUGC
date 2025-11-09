//! Gadgets for Full STARK Verifier
//!
//! Implementations for:
//! - Light RPO-256 (congruence-only Goldilocks operations)
//! - DEEP combiner (RandomRho & DegreeChunks)
//! - Full FRI verification (multi-layer with consistency and folding)
//! - GL value range checks for input validation

pub mod gl_range;      // Input validation and canonicalization at boundaries
pub mod gl_fast;       // Light GL operations using congruence checks
pub mod rpo_gl_light;  // Light RPO-256 implementation
pub mod fri;           // FRI layer verification
pub mod utils;         // Utility functions (digest conversion, etc.)
pub mod merkle_batch;  // Batch Merkle verification (Winterfell get_root in-circuit)

