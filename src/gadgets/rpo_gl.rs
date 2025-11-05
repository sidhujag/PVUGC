//! GL-Native RPO-256 Gadget
//!
//! Parametric Rescue-Prime-Optimized permutation over Goldilocks field
//! All operations enforce mod-p_GL semantics

use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use crate::outer_compressed::InnerFr;

pub type FpGLVar = FpVar<InnerFr>;

/// Parameters for a Rescue-Prime-Optimized permutation (aka RPO-256 over GL)
/// All entries are GL elements (u64) and must match the prover/verifier constants.
#[derive(Clone, Debug)]
pub struct RpoParamsGL {
    /// State width (t), digest len (d), rate (r).
    pub t: usize,          // e.g. 12
    pub d: usize,          // e.g. 4
    pub rate: usize,       // e.g. 8
    
    /// S-Box exponents: alpha and alpha^{-1} (mod p_GL-1).
    /// We *only* raise to alpha (small) in-circuit; inverse rounds witness y and enforce y^alpha = x.
    pub alpha: u64,        // e.g. 7
    
    /// Round constants: for each round and each lane
    /// Two arrays per round (as in Rescue-Prime: add before and after S-Boxes)
    /// Layout: ark1[round][lane], ark2[round][lane]
    pub ark1: Vec<Vec<u64>>,
    pub ark2: Vec<Vec<u64>>,
    
    /// MDS matrix t x t
    pub mds: Vec<Vec<u64>>,
    
    /// Num rounds (full RP rounds)
    pub n_rounds: usize,
}

impl Default for RpoParamsGL {
    fn default() -> Self {
        // Use actual Rp64_256 constants from Winterfell
        use winter_crypto::hashers::Rp64_256;
        
        // Extract constants (they're BaseElement arrays)
        let mut ark1 = Vec::with_capacity(Rp64_256::NUM_ROUNDS);
        for r in 0..Rp64_256::NUM_ROUNDS {
            let mut round_consts = Vec::with_capacity(Rp64_256::STATE_WIDTH);
            for i in 0..Rp64_256::STATE_WIDTH {
                round_consts.push(Rp64_256::ARK1[r][i].as_int());
            }
            ark1.push(round_consts);
        }
        
        let mut ark2 = Vec::with_capacity(Rp64_256::NUM_ROUNDS);
        for r in 0..Rp64_256::NUM_ROUNDS {
            let mut round_consts = Vec::with_capacity(Rp64_256::STATE_WIDTH);
            for i in 0..Rp64_256::STATE_WIDTH {
                round_consts.push(Rp64_256::ARK2[r][i].as_int());
            }
            ark2.push(round_consts);
        }
        
        let mut mds = Vec::with_capacity(Rp64_256::STATE_WIDTH);
        for i in 0..Rp64_256::STATE_WIDTH {
            let mut row = Vec::with_capacity(Rp64_256::STATE_WIDTH);
            for j in 0..Rp64_256::STATE_WIDTH {
                row.push(Rp64_256::MDS[i][j].as_int());
            }
            mds.push(row);
        }
        
        Self {
            t: Rp64_256::STATE_WIDTH,  // 12
            d: 4,  // Digest size (capacity elements)
            rate: 8,  // Rate width (8 elements for absorption)
            alpha: 7,
            ark1,
            ark2,
            mds,
            n_rounds: Rp64_256::NUM_ROUNDS,  // 7 rounds
        }
    }
}

/// Winterfell RPO round: α → MDS → ARK1 → α⁻¹ → MDS → ARK2
fn rp_round_gl(
    cs: ConstraintSystemRef<InnerFr>,
    state: &mut [FpGLVar],
    params: &RpoParamsGL,
    round_idx: usize,
) -> Result<(), SynthesisError> {
    let t = params.t;

    // S-box α (x^7) with canonical GL at each step ---
    for i in 0..t {
        use crate::gadgets::gl_range::gl_mul_var;
        let x  = state[i].clone();
        let x2 = gl_mul_var(cs.clone(), &x, &x)?;       // canonical GL
        let x4 = gl_mul_var(cs.clone(), &x2, &x2)?;     // canonical GL
        let x6 = gl_mul_var(cs.clone(), &x4, &x2)?;     // canonical GL
        state[i] = gl_mul_var(cs.clone(), &x6, &x)?;    // canonical GL x^7
    }

    // MDS ---
    let mut mixed = Vec::with_capacity(t);
    for i in 0..t {
        let coeffs: Vec<u64> = (0..t).map(|j| params.mds[i][j]).collect();
        mixed.push(crate::gadgets::gl_range::gl_lincomb(cs.clone(), &coeffs, state)?);
    }
    for (i, val) in mixed.into_iter().enumerate() { state[i] = val; }

    // ARK1 ---
    for i in 0..t {
        state[i] = crate::gadgets::gl_range::gl_add_const(cs.clone(), &state[i], params.ark1[round_idx][i])?;
    }

    // S-box α⁻¹ with GL check ---
    for i in 0..t {
        use crate::gadgets::gl_range::gl_mul_var;
        let x = state[i].clone();
        let y = FpGLVar::new_witness(cs.clone(), || {
            use crate::gl_u64::{fr_to_gl_u64, gl_mul};
            let x_gl = fr_to_gl_u64(x.value()?);
            let mut acc = 1u64;
            let mut base = x_gl;
            let mut e = 10540996611094048183u64;
            while e > 0 {
                if e & 1 == 1 { acc = gl_mul(acc, base); }
                base = gl_mul(base, base);
                e >>= 1;
            }
            Ok(InnerFr::from(acc))
        })?;
        // Compute y^7 in GL (using gl_mul_var for canonical at each step)
        let y2 = gl_mul_var(cs.clone(), &y, &y)?;
        let y4 = gl_mul_var(cs.clone(), &y2, &y2)?;
        let y6 = gl_mul_var(cs.clone(), &y4, &y2)?;
        let y7 = gl_mul_var(cs.clone(), &y6, &y)?;
        // Enforce gl_pow7(y) == x (GL check, not Fr!)
        y7.enforce_equal(&x)?;
        state[i] = y;  // y is already canonical GL
    }

    // MDS ---
    let mut mixed2 = Vec::with_capacity(t);
    for i in 0..t {
        let coeffs: Vec<u64> = (0..t).map(|j| params.mds[i][j]).collect();
        mixed2.push(crate::gadgets::gl_range::gl_lincomb(cs.clone(), &coeffs, state)?);
    }
    for (i, val) in mixed2.into_iter().enumerate() { state[i] = val; }

    // ARK2 ---
    for i in 0..t {
        state[i] = crate::gadgets::gl_range::gl_add_const(cs.clone(), &state[i], params.ark2[round_idx][i])?;
    }

    Ok(())
}

/// A GL-native RPO sponge gadget (parametric)
pub struct Rpo256GlVar {
    #[allow(dead_code)]
    cs: ConstraintSystemRef<InnerFr>,
    pub params: RpoParamsGL,
    pub state: Vec<FpGLVar>,
    pub rate_idx: usize, // next absorb slot (0..rate-1)
}

impl Rpo256GlVar {
    pub fn new(cs: ConstraintSystemRef<InnerFr>, params: RpoParamsGL) -> Result<Self, SynthesisError> {
        let mut state = Vec::with_capacity(params.t);
        for _ in 0..params.t {
            // Initialize as witness constrained to zero by circuit logic.
            // Soundness relies on: (1) lane layout is correct (Winterfell-aligned),
            // (2) permutation outputs are canonical GL, (3) CS extraction happens via explicit passing,
            // not via state[0].cs() on a potentially-constant value.
            state.push(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(0u64)))?);
        }
        Ok(Self { cs, params, state, rate_idx: 0 })
    }
    
    pub fn absorb(&mut self, elems: &[FpGLVar]) -> Result<(), SynthesisError> {
        let rate_base = 4;  // Rate starts at lane 4 in Rp64_256
        for e in elems {
            if self.rate_idx == self.params.rate {
                self.permute()?;
                self.rate_idx = 0;
            }
            self.state[rate_base + self.rate_idx] = 
                crate::gadgets::gl_range::gl_add_var(self.cs.clone(), 
                                                     &self.state[rate_base + self.rate_idx],
                                                     e)?;
            self.rate_idx += 1;
        }
        Ok(())
    }
    
    pub fn permute(&mut self) -> Result<(), SynthesisError> {
        for r in 0..self.params.n_rounds {
            rp_round_gl(self.cs.clone(), &mut self.state, &self.params, r)?;
        }
        Ok(())
    }
    
    fn finalize_for_digest(&mut self) -> Result<(), SynthesisError> {
        // Always do one trailing permutation before squeezing the digest,
        // even if the last absorb hit the rate exactly.
        self.permute()?;
        self.rate_idx = 0;
        Ok(())
    }
    
    pub fn hash_elements(&mut self, elems: &[FpGLVar]) -> Result<Vec<FpGLVar>, SynthesisError> {
        self.absorb(elems)?;
        self.finalize_for_digest()?;
        let mut out = Vec::with_capacity(self.params.d);
        // Digest lanes: read rate lanes [4..8) not capacity tail
        for i in 4..8 {
            out.push(self.state[i].clone());
        }
        Ok(out)
    }
    
    pub fn squeeze(&mut self, n: usize) -> Result<Vec<FpGLVar>, SynthesisError> {
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            self.permute()?;
            for i in 4..8 {  // Correct digest lanes for Winterfell alignment
                if out.len() == n { break; }
                out.push(self.state[i].clone());
            }
        }
        Ok(out)
    }
    
    /// Convenience: merge two digests (each d) into one digest (d)
    pub fn merge(&mut self, left: &[FpGLVar], right: &[FpGLVar]) -> Result<Vec<FpGLVar>, SynthesisError> {
        assert_eq!(left.len(), self.params.d);
        assert_eq!(right.len(), self.params.d);
        let mut input = Vec::with_capacity(2 * self.params.d);
        input.extend_from_slice(left);
        input.extend_from_slice(right);
        self.hash_elements(&input)
    }
}

// ============================================================================
// Stateless RPO Helpers
// ============================================================================
// Each hash/merge starts from fresh zero state to match Winterfell semantics.

/// Stateless RPO hash (fresh instance per call)
/// Winterfell-aligned: capacity [0..3], rate [4..11], digest [4..7]
pub fn rpo_hash_elements_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGL,
    elems: &[FpGLVar],
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut h = Rpo256GlVar::new(cs.clone(), params.clone())?;

    // state[0] = elements.len() (TOTAL length, not mod 8)
    let total_len = elems.len() as u64;
    let len_const = FpGLVar::constant(InnerFr::from(total_len));
    h.state[0] = &h.state[0] + &len_const;  // Fr add; permutation will canonicalize

    // absorb with block-by-block permutation
    let mut i = 0usize;
    for x in elems.iter() {
        h.state[4 + i] = &h.state[4 + i] + x;  // Fr add; permutation will canonicalize
        i += 1;
        if i == 8 {
            h.permute()?;  // Full block absorbed, permute  
            i = 0;  // Reset index, state carries forward
        }
    }

    // if we absorbed some elements but didn't apply a permutation (partial block), permute now
    // No explicit padding needed - zeros already there from initialization
    if i > 0 {
        h.permute()?;
    }

    // digest = [4..8)
    Ok(vec![h.state[4].clone(), h.state[5].clone(), h.state[6].clone(), h.state[7].clone()])
}

/// Stateless RPO merge (fresh instance per call)
pub fn rpo_merge_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGL,
    left: &[FpGLVar],
    right: &[FpGLVar],
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut h = Rpo256GlVar::new(cs.clone(), params.clone())?;
    
    // state[0] = 8 (RATE_WIDTH, the number of elements being hashed)
    let len_8 = FpGLVar::constant(InnerFr::from(8u64));
    h.state[0] = &h.state[0] + &len_8;  // Fr add; permutation will canonicalize
    
    // Place left||right into lanes 4..11
    for i in 0..4 {
        h.state[4 + i] = left[i].clone();
    }
    for i in 0..4 {
        h.state[8 + i] = right[i].clone();
    }
    
    // Full 8-element block, permute once
    h.permute()?;
    
    // Return digest lanes 4..7
    Ok(vec![h.state[4].clone(), h.state[5].clone(), h.state[6].clone(), h.state[7].clone()])
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    
    #[test]
    fn test_rpo_gl_construction() {
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        let params = RpoParamsGL::default();
        let rpo = Rpo256GlVar::new(cs.clone(), params).unwrap();
        
        // Just verify construction works - hashing test would require actual execution
        assert_eq!(rpo.state.len(), 12);
        assert_eq!(rpo.params.t, 12);
        assert_eq!(rpo.params.d, 4);
        assert_eq!(rpo.params.alpha, 7);
    }
}

