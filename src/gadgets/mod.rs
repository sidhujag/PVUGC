//! Gadgets for Full STARK Verifier
//!
//! Expert-provided implementations for:
//! - GL-native RPO-256 (parametric)
//! - DEEP combiner weights (RandomRho & DegreeChunks)
//! - Full FRI verification (L>0 with consistency+fold)
//! - GL value range checks (< p_GL)

pub mod gl_range;
pub mod combiner;
pub mod rpo_gl;
pub mod fri;
pub mod utils;

