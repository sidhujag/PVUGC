//! DEEP Combiner Weights
//!
//! Supports RandomRho and DegreeChunks weighting schemes for composition polynomials

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

/// Compute combiner weights w_i(x) for i=0..n-1
/// - For RandomRho: x is ignored; rho is required
/// - For DegreeChunks: rho is ignored; x is required
pub fn combiner_weights(
    kind: CombinerKind,
    n: usize,
    x: Option<&FpGLVar>,
    rho: Option<&FpGLVar>,
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut w = Vec::with_capacity(n);
    match kind {
        CombinerKind::RandomRho => {
            let rho = rho.expect("rho required for RandomRho");
            let mut pow = FpGLVar::constant(InnerFr::from(1u64));
            for _ in 0..n {
                w.push(pow.clone());
                pow = &pow * rho;
            }
        }
        CombinerKind::DegreeChunks { chunk_deg } => {
            let x = x.expect("x required for DegreeChunks");
            if chunk_deg == 0 { return Err(SynthesisError::AssignmentMissing); }
            let mut pow = FpGLVar::constant(InnerFr::from(1u64));
            let x_pow_chunk = pow_x_small(x, chunk_deg)?;
            for _ in 0..n {
                w.push(pow.clone());
                pow = &pow * &x_pow_chunk;
            }
        }
    }
    Ok(w)
}

/// Helper: x^k with small k (<= few thousands acceptable). Uses square-and-multiply.
pub fn pow_x_small(x: &FpGLVar, k: usize) -> Result<FpGLVar, SynthesisError> {
    if k == 0 { return Ok(FpGLVar::constant(InnerFr::from(1u64))); }
    let mut res = FpGLVar::constant(InnerFr::from(1u64));
    let mut base = x.clone();
    let mut e = k;
    while e > 0 {
        if e & 1 == 1 { res = &res * &base; }
        base = &base * &base;
        e >>= 1;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    
    #[test]
    fn test_combiner_weights_randomrho() {
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        let x = FpGLVar::one();
        let rho = FpGLVar::constant(InnerFr::from(7u64));
        let w = combiner_weights(CombinerKind::RandomRho, 4, Some(&x), Some(&rho)).unwrap();
        assert_eq!(w.len(), 4);
        assert!(cs.is_satisfied().unwrap());
    }
    
    #[test]
    fn test_combiner_weights_degree_chunks() {
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        let x = FpGLVar::constant(InnerFr::from(2u64));
        let w = combiner_weights(
            CombinerKind::DegreeChunks { chunk_deg: 3 }, 
            4, 
            Some(&x), 
            None
        ).unwrap();
        assert_eq!(w.len(), 4);
        // Weights should be: 1, x^3, x^6, x^9
        assert!(cs.is_satisfied().unwrap());
    }
}

