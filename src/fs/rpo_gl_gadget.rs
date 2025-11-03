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

fn gl_from_le_bytes(bytes: &[UInt8<InnerFr>]) -> Result<FpGLVar, SynthesisError> {
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


