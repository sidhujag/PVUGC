use ark_relations::r1cs::{SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use crate::outer_compressed::InnerFr;

pub type FpGLVar = FpVar<InnerFr>;
#[derive(Clone, Copy, Debug)]
pub enum CombinerKind {
    RandomRho,                          // weights = rho^i
    DegreeChunks { chunk_deg: usize },  // weights = x^(chunk_deg * i)
}
/// Convert 32 bytes to 4 GL field elements (8 bytes each, LE)
pub fn digest32_to_gl4(bytes32: &[UInt8<InnerFr>]) -> Result<[FpGLVar;4], SynthesisError> {
    assert!(bytes32.len() == 32);
    let a0 = bytes_to_gl(&bytes32[0..8])?;
    let a1 = bytes_to_gl(&bytes32[8..16])?;
    let a2 = bytes_to_gl(&bytes32[16..24])?;
    let a3 = bytes_to_gl(&bytes32[24..32])?;
    Ok([a0, a1, a2, a3])
}

/// Convert 8 LE bytes to GL field element
fn bytes_to_gl(bytes: &[UInt8<InnerFr>]) -> Result<FpGLVar, SynthesisError> {
    if bytes.is_empty() {
        return Ok(FpGLVar::constant(InnerFr::from(0u64)));
    }
    // Get CS from first byte
    let cs = bytes[0].cs();
    let mut acc = FpGLVar::new_constant(cs.clone(), InnerFr::from(0u64))?;
    let mut pow = FpGLVar::new_constant(cs.clone(), InnerFr::from(1u64))?;
    let base = FpGLVar::constant(InnerFr::from(256u64));
    for b in bytes {
        acc = &acc + &(&b.to_fp()? * &pow);
        pow = &pow * &base;
    }
    Ok(acc)
}


