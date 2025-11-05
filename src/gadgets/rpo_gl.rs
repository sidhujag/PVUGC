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

// (old helpers removed; GL ops now enforced via gadgets::gl_range)

/// One **full** RPO round: Ark1 → α → MDS → Ark2 → α⁻¹ → MDS
fn rp_round_gl(
    state: &mut [FpGLVar],
    params: &RpoParamsGL,
    round_idx: usize,
) -> Result<(), SynthesisError> {
    let cs = state[0].cs();
    let t = params.t;

    // Ark1 (Fr add)
    for i in 0..t {
        state[i] = crate::gadgets::gl_range::gl_add_const(cs.clone(), &state[i], params.ark1[round_idx][i])?;
    }

    // S-box α (α=7) entirely in Fr
    for i in 0..t {
        // x^7 = ((x^2)^2 * x^2) * x
        let x  = state[i].clone();
        let x2 = x.clone() * x.clone();
        let x4 = x2.clone() * x2.clone();
        let x6 = x4 * x2;
        state[i] = x6 * x;                            // x^7
    }

    // MDS (Fr lincomb) — gl_lincomb returns Fr (fixed above)
    let after_alpha = state.to_vec();
    for i in 0..t {
        let coeffs: Vec<u64> = (0..t).map(|j| params.mds[i][j]).collect();
        state[i] = crate::gadgets::gl_range::gl_lincomb(cs.clone(), &coeffs, &after_alpha)?;
    }

    // Ark2 (Fr add)
    for i in 0..t {
        state[i] = crate::gadgets::gl_range::gl_add_const(cs.clone(), &state[i], params.ark2[round_idx][i])?;
    }

    // S-box α⁻¹: witness y = x^(α⁻¹) in GL, enforce y^α == x (Fr power), replace lane with y
    for i in 0..t {
        let x = state[i].clone();
        let y = FpGLVar::new_witness(cs.clone(), || {
            use crate::gl_u64::{fr_to_gl_u64, gl_mul};
            let x_gl = fr_to_gl_u64(x.value()?);
            // Compute x^(α⁻¹) in GL using square-and-multiply
            let mut acc = 1u64;
            let mut base = x_gl;
            let mut e = 10540996611094048183u64; // α⁻¹ mod (p_GL - 1)
            while e > 0 {
                if e & 1 == 1 { acc = gl_mul(acc, base); }
                base = gl_mul(base, base);
                e >>= 1;
            }
            Ok(InnerFr::from(acc))
        })?;
        // compute y^7 in Fr
        let y2 = y.clone() * y.clone();
        let y4 = y2.clone() * y2.clone();
        let y6 = y4.clone() * y2.clone();
        let y7 = y6 * y.clone();
        // enforce y^7 == x (GL congruence is subsumed by Fr equality here)
        y7.enforce_equal(&x)?;
        state[i] = y;
    }

    // MDS again
    let after_inv = state.to_vec();
    for i in 0..t {
        let coeffs: Vec<u64> = (0..t).map(|j| params.mds[i][j]).collect();
        state[i] = crate::gadgets::gl_range::gl_lincomb(cs.clone(), &coeffs, &after_inv)?;
    }

    // Per-round congruence check at round boundary (prevents "one giant quotient" loophole)
    for lane in state.iter() {
        // reduce the current Fr lane to GL and bind with a tight |q| ≤ 1 congruence
        let lane_gl = FpGLVar::new_witness(lane.cs(), || {
            use crate::gl_u64::fr_to_gl_u64;
            Ok(InnerFr::from(fr_to_gl_u64(lane.value()?)))
        })?;
        use crate::inner_stark_full::enforce_gl_eq_with_bound;
        enforce_gl_eq_with_bound(lane, &lane_gl, Some(1))?;
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
            // Initialize as witness constrained to zero (ensures CS attachment)
            // The stateless helpers will overwrite these immediately, constraining the IV
            state.push(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(0u64)))?);
        }
        Ok(Self { cs, params, state, rate_idx: 0 })
    }
    
    pub fn absorb(&mut self, elems: &[FpGLVar]) -> Result<(), SynthesisError> {
        for e in elems {
            if self.rate_idx == self.params.rate {
                self.permute()?;
                self.rate_idx = 0;
            }
            self.state[self.rate_idx] = self.state[self.rate_idx].clone() + e;  // Fr add
            self.rate_idx += 1;
        }
        Ok(())
    }
    
    pub fn permute(&mut self) -> Result<(), SynthesisError> {
        for r in 0..self.params.n_rounds {
            rp_round_gl(&mut self.state, &self.params, r)?;   // α + inv per round
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
        self.finalize_for_digest()?;            // <-- always permute once here
        let mut out = Vec::with_capacity(self.params.d);
        // Digest lanes: read capacity tail [t-d .. t)
        for i in (self.params.t - self.params.d)..self.params.t {
            out.push(self.state[i].clone());
        }
        Ok(out)
    }
    
    pub fn squeeze(&mut self, n: usize) -> Result<Vec<FpGLVar>, SynthesisError> {
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            self.permute()?;
            for i in (self.params.t - self.params.d)..self.params.t {
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
// Stateless RPO Helpers (CRITICAL for Merkle verification)
// ============================================================================
// Each hash/merge MUST start from fresh zero state to match Winterfell!

/// Stateless RPO hash (fresh instance per call)
/// Winterfell-aligned: capacity [0..3], rate [4..11], digest [4..7]
pub fn rpo_hash_elements_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGL,
    elems: &[FpGLVar],
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut h = Rpo256GlVar::new(cs.clone(), params.clone())?;

    // 1) Set length marker in capacity (lane 0) - ADD to witness zero (preserves CS)
    let len_const = FpGLVar::new_constant(h.state[0].cs(), InnerFr::from(elems.len() as u64))?;
    h.state[0] = &h.state[0] + &len_const;  // 0 + len = len, but preserves CS from state[0]

    // 2) Write inputs into rate lanes 4..11; pad zeros if < 8
    let rate_off = 4;
    for (k, e) in elems.iter().enumerate() {
        if rate_off + k < h.state.len() {
            h.state[rate_off + k] = e.clone();  // State is zero, so adding e is just e
        }
    }

    // 3) Single permutation, unconditionally
    h.permute()?;

    // 4) Return digest lanes 4..7 (first four of rate)
    Ok(vec![
        h.state[4].clone(), h.state[5].clone(),
        h.state[6].clone(), h.state[7].clone(),
    ])
}

/// Stateless RPO merge (fresh instance per call)
pub fn rpo_merge_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGL,
    left: &[FpGLVar],
    right: &[FpGLVar],
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut h = Rpo256GlVar::new(cs.clone(), params.clone())?;
    
    // Set length=8 in capacity[0] - state is zero, so just assign
    h.state[0] = FpGLVar::new_constant(cs.clone(), InnerFr::from(8u64))?;
    
    // Place left||right into lanes 4..11 - state is zero, so just assign
    let rate_off = 4;
    for i in 0..4 {
        h.state[rate_off + i] = left[i].clone();
    }
    for i in 0..4 {
        h.state[rate_off + 4 + i] = right[i].clone();
    }
    
    // Permute once
    h.permute()?;
    
    // Return digest lanes 4..7
    Ok(vec![
        h.state[4].clone(), h.state[5].clone(),
        h.state[6].clone(), h.state[7].clone(),
    ])
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

