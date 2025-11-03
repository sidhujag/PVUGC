use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::uint8::UInt8;
use ark_r1cs_std::fields::FieldVar;

use crate::inner_stark::{FpGL, FpGLVar};
use crate::outer_compressed::InnerFr;
use crate::fs::rpo_gl_constants::*;

pub struct RpoGlSpongeVar { pub state: Vec<FpGLVar> }

impl RpoGlSpongeVar {
    pub fn new(_cs: ConstraintSystemRef<InnerFr>) -> Result<Self, SynthesisError> {
        // NOTE: CS type param unused; callers should pass InnerFr CS; we reuse the handle
        let w = rpo_state_width();
        let mut lanes = Vec::with_capacity(w);
        for _ in 0..w {
            lanes.push(FpGLVar::zero());
        }
        Ok(Self { state: lanes })
    }

    pub fn absorb_bytes(&mut self, bytes: &[UInt8<InnerFr>]) -> Result<(), SynthesisError> {
        // 8 bytes per GL limb, little-endian; add to state lanes round-robin
        let mut lane = 0usize;
        let w = rpo_state_width();
        for chunk in bytes.chunks(8) {
            let limb = gl_from_le_bytes(chunk)?;
            self.state[lane] = &self.state[lane] + &limb;
            lane = (lane + 1) % w;
        }
        Ok(())
    }

    pub fn permute(&mut self) -> Result<(), SynthesisError> {
        let w = rpo_state_width();
        let ark1 = rpo_ark1_rows_u64();
        let ark2 = rpo_ark2_rows_u64();
        let full_rounds = ark1.len();
        let total_rounds = full_rounds; // rescue split handled by ARK1/ARK2
        // For each round: add ARK1, S-box (alpha), MDS; then add ARK2, inverse S-box (inv alpha), MDS
        for r in 0..total_rounds {
            // ARK
            for i in 0..w {
                let c = FpGLVar::constant(FpGL::from(*ark1.get(r).and_then(|row| row.get(i)).unwrap_or(&0u64)));
                self.state[i] = &self.state[i] + &c;
            }
            // S-box x^alpha
            for i in 0..w {
                self.state[i] = exp_alpha(&self.state[i], rpo_alpha());
            }
            // MDS
            self.apply_mds()?;
            // Second half: ARK2 + inverse S-box + MDS
            for i in 0..w {
                let c = FpGLVar::constant(FpGL::from(*ark2.get(r).and_then(|row| row.get(i)).unwrap_or(&0u64)));
                self.state[i] = &self.state[i] + &c;
            }
            for i in 0..w {
                self.state[i] = exp_alpha(&self.state[i], rpo_inv_alpha());
            }
            self.apply_mds()?;
        }
        Ok(())
    }

    fn apply_mds(&mut self) -> Result<(), SynthesisError> {
        let cur = self.state.clone();
        let w = rpo_state_width();
        let mds = rpo_mds_rows_u64();
        let mut next: Vec<FpGLVar> = Vec::with_capacity(w);
        for row in 0..w {
            let mut acc = FpGLVar::zero();
            for col in 0..w {
                let c = FpGLVar::constant(FpGL::from(*mds.get(row).and_then(|r| r.get(col)).unwrap_or(&0u64)));
                acc = acc + &(cur[col].clone() * c);
            }
            next.push(acc);
        }
        self.state = next;
        Ok(())
    }

    pub fn squeeze(&mut self) -> Result<FpGLVar, SynthesisError> {
        let out = self.state[0].clone();
        self.permute()?;
        Ok(out)
    }
}

/// Rp64_256 hash gadget over embedded Goldilocks (matches winterfell-pvugc/crypto Rp64_256)
pub struct Rpo256Var { pub state: Vec<FpGLVar> }

impl Rpo256Var {
    pub fn new(_cs: ConstraintSystemRef<InnerFr>) -> Result<Self, SynthesisError> {
        let w = rpo_state_width();
        Ok(Self { state: vec![FpGLVar::zero(); w] })
    }

    #[inline]
    fn apply_mds(&mut self) -> Result<(), SynthesisError> {
        let cur = self.state.clone();
        let w = rpo_state_width();
        let mds = rpo_mds_rows_u64();
        let mut next: Vec<FpGLVar> = Vec::with_capacity(w);
        for row in 0..w {
            let mut acc = FpGLVar::zero();
            for col in 0..w {
                let c = FpGLVar::constant(FpGL::from(*mds.get(row).and_then(|r| r.get(col)).unwrap_or(&0u64)));
                acc = acc + &(cur[col].clone() * c);
            }
            next.push(acc);
        }
        self.state = next;
        Ok(())
    }

    fn add_constants(&mut self, ark_rows: &[&[u64]]) {
        for (i, lane) in self.state.iter_mut().enumerate() {
            let mut acc = FpGLVar::zero();
            for row in ark_rows.iter() {
                let c = FpGLVar::constant(FpGL::from(row.get(i).copied().unwrap_or(0)));
                acc = acc + c;
            }
            *lane = lane.clone() + acc;
        }
    }

    fn round(&mut self, round_idx: usize) -> Result<(), SynthesisError> {
        // first half: S-box (alpha), MDS, ARK1
        for i in 0..self.state.len() { self.state[i] = exp_alpha(&self.state[i], rpo_alpha()); }
        self.apply_mds()?;
        // ARK1 row addition
        let ark1 = rpo_ark1_rows_u64();
        for i in 0..self.state.len() {
            let c = FpGLVar::constant(FpGL::from(*ark1.get(round_idx).and_then(|row| row.get(i)).unwrap_or(&0u64)));
            self.state[i] = self.state[i].clone() + c;
        }
        // second half: inverse S-box, MDS, ARK2
        for i in 0..self.state.len() { self.state[i] = exp_alpha(&self.state[i], rpo_inv_alpha()); }
        self.apply_mds()?;
        let ark2 = rpo_ark2_rows_u64();
        for i in 0..self.state.len() {
            let c = FpGLVar::constant(FpGL::from(*ark2.get(round_idx).and_then(|row| row.get(i)).unwrap_or(&0u64)));
            self.state[i] = self.state[i].clone() + c;
        }
        Ok(())
    }

    pub fn permute(&mut self) -> Result<(), SynthesisError> {
        let rounds = rpo_ark1_rows_u64().len();
        for r in 0..rounds { self.round(r)?; }
        Ok(())
    }

    /// Hash elements (ElementHasher::hash_elements):
    /// - capacity[0] = len
    /// - absorb into rate lanes 4..11, apply permutation on full rate
    pub fn hash_elements(&mut self, elems: &[FpGLVar]) -> Result<[FpGLVar; 4], SynthesisError> {
        let rate_start = 4usize; let rate_width = 8usize;
        self.state = vec![FpGLVar::zero(); rpo_state_width()];
        self.state[0] = FpGLVar::constant(FpGL::from(elems.len() as u64));
        let mut i = 0usize;
        for e in elems {
            let idx = rate_start + i;
            self.state[idx] = self.state[idx].clone() + e.clone();
            i += 1;
            if i % rate_width == 0 { self.permute()?; i = 0; }
        }
        if i > 0 { self.permute()?; }
        Ok([
            self.state[4].clone(),
            self.state[5].clone(),
            self.state[6].clone(),
            self.state[7].clone(),
        ])
    }

    /// Merge two digests (each 4 elements) per Rp64_256::merge semantics
    pub fn merge(&mut self, left: &[FpGLVar;4], right: &[FpGLVar;4]) -> Result<[FpGLVar;4], SynthesisError> {
        self.state = vec![FpGLVar::zero(); rpo_state_width()];
        // rate[4..12] = left||right (8 elems)
        self.state[4] = left[0].clone();
        self.state[5] = left[1].clone();
        self.state[6] = left[2].clone();
        self.state[7] = left[3].clone();
        self.state[8] = right[0].clone();
        self.state[9] = right[1].clone();
        self.state[10] = right[2].clone();
        self.state[11] = right[3].clone();
        // capacity[0] = 8 (number of elements hashed)
        self.state[0] = FpGLVar::constant(FpGL::from(8u64));
        self.permute()?;
        Ok([
            self.state[4].clone(),
            self.state[5].clone(),
            self.state[6].clone(),
            self.state[7].clone(),
        ])
    }
}

/// Helper: decode 32-byte digest into 4 GL field elements (8-byte LE each)
pub fn digest32_to_gl4(bytes32: &[UInt8<InnerFr>]) -> Result<[FpGLVar;4], SynthesisError> {
    assert!(bytes32.len() == 32);
    let a0 = gl_from_le_bytes(&bytes32[0..8])?;
    let a1 = gl_from_le_bytes(&bytes32[8..16])?;
    let a2 = gl_from_le_bytes(&bytes32[16..24])?;
    let a3 = gl_from_le_bytes(&bytes32[24..32])?;
    Ok([a0,a1,a2,a3])
}

fn exp_alpha(x: &FpGLVar, alpha: u64) -> FpGLVar {
    // Optimized for small exponents, fallback to square-and-multiply for large ones (e.g., inv alpha)
    if alpha == 5 {
        let x2 = x * x; let x4 = &x2 * &x2; return x4 * x;
    }
    if alpha == 7 {
        let x2 = x * x; let x4 = &x2 * &x2; return x4 * &x2 * x;
    }
    // Fallback: square-and-multiply by bits of alpha
    let mut res = FpGLVar::one();
    let mut base = x.clone();
    let mut e = alpha;
    while e > 0 {
        if (e & 1) == 1 { res = &res * &base; }
        base = &base * &base; e >>= 1;
    }
    res
}

pub fn gl_from_le_bytes(bytes: &[UInt8<InnerFr>]) -> Result<FpGLVar, SynthesisError> {
    // Interpret bytes as a little-endian integer in the (Goldilocks-as-embedded) field,
    // using *constrained* conversions. No reading .value(), no constants.
    let mut acc = FpGLVar::zero();
    let mut pow = FpGLVar::constant(FpGL::from(1u64));
    let base = FpGLVar::constant(FpGL::from(256u64));

    for b in bytes {
        // Constrained: converts UInt8 to FpVar<InnerFr> via gadget relation.
        let b_as_field = b.to_fp()?;
        acc = acc + &(b_as_field * pow.clone());
        pow = pow * base.clone();
    }
    Ok(acc)
}


