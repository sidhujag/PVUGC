//! Gadgets for Full STARK Verifier
//!
//! Implementations for:
//! - Light RPO-256 (congruence-only Goldilocks operations)
//! - DEEP combiner (RandomRho & DegreeChunks)
//! - Full FRI verification (multi-layer with consistency and folding)
//! - GL value range checks for input validation

pub mod fri; // FRI layer verification
pub mod gl_fast; // Light GL operations using congruence checks
pub mod gl_range; // Input validation and canonicalization at boundaries
pub mod merkle_batch;
pub mod rpo_gl_light; // Light RPO-256 implementation
pub mod utils; // Utility functions (digest conversion, etc.) // Batch Merkle verification (Winterfell get_root in-circuit)
