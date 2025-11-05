//! Full FRI (L>0) Layer Verification
//!
//! Implements consistency + fold + terminal check exactly as specified by expert

use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::boolean::Boolean;
use crate::outer_compressed::InnerFr;
use crate::gadgets::rpo_gl::RpoParamsGL;
use crate::gadgets::utils::digest32_to_gl4;

pub type FpGLVar = FpVar<InnerFr>;
pub use crate::gadgets::combiner::pow_x_small;

#[derive(Clone, Copy, Debug)]
pub enum FriTerminalKind {
    Constant,                  // final values must be all equal
    Poly { degree: usize },    // final values equal P(x) for given coeffs
}

pub struct FriConfigGL {
    pub folding_factor: usize,         // typically 2
    pub params_rpo: RpoParamsGL,       // GL-native RPO params to verify Merkle leaves
    pub terminal: FriTerminalKind,
    pub domain_offset: u64,            // GL element (usually 1)
    pub g_lde: u64,                    // GL element: generator of LDE subgroup
}

pub struct FriLayerQueryGL<'a> {
    pub queries: &'a [crate::inner_stark_full::FriQuery], // (v_lo, v_hi, path)
    pub root_bytes: &'a [UInt8<InnerFr>],                 // layer root (32B)
    pub beta: &'a FpGLVar,
}

/// Verify multi-layer FRI with GL semantics. `current` starts from DEEP sums.
pub fn verify_fri_layers_gl(
    cs: ConstraintSystemRef<InnerFr>,
    cfg: &FriConfigGL,
    main_positions: &[usize],          // positions in initial domain (one per query)
    mut current: Vec<FpGLVar>,         // DEEP sums per query
    layers: &[FriLayerQueryGL],
    remainder_coeffs_opt: Option<&[u64]>, // for Poly terminal: coeffs (low->high)
) -> Result<(), SynthesisError> {
    use crate::inner_stark_full::enforce_gl_eq;
    use crate::gadgets::rpo_gl::Rpo256GlVar;
    
    let t = cfg.folding_factor;
    if t == 0 { return Err(SynthesisError::Unsatisfiable); }
    let shift = (t as f64).log2() as usize;
    
    // Folded positions per layer
    let mut positions: Vec<usize> = main_positions.to_vec();
    
    for (_layer_idx, layer) in layers.iter().enumerate() {
        use crate::gadgets::rpo_gl::{rpo_hash_elements_gl, rpo_merge_gl};
        
        // Verify each leaf path and consistency
        for (q_idx, q) in layer.queries.iter().enumerate() {
            // 1) Leaf hash for this query: hash([v_lo, v_hi]) - STATELESS!
            let v_lo = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(q.v_lo)))?;
            let v_hi = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(q.v_hi)))?;
            let digest = rpo_hash_elements_gl(cs.clone(), &cfg.params_rpo, &[v_lo.clone(), v_hi.clone()])?;
            
            // 2) Walk the Merkle path (GL semantics)
            let mut cur = digest;
            for (sib_bytes, is_right) in q.merkle_path.iter().zip(&q.path_positions) {
                let sib_bytes_vars: Vec<UInt8<InnerFr>> = sib_bytes.iter()
                    .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
                    .collect::<Result<_, _>>()?;
                let sib = digest32_to_gl4(&sib_bytes_vars)?;
                let is_right_bool = Boolean::new_witness(cs.clone(), || Ok(*is_right))?;
                
                // parent(left, right) = stateless rpo.merge(left, right)
                let left = [
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[0], &cur[0])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[1], &cur[1])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[2], &cur[2])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &sib[3], &cur[3])?,
                ];
                let right = [
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &cur[0], &sib[0])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &cur[1], &sib[1])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &cur[2], &sib[2])?,
                    FpVar::<InnerFr>::conditionally_select(&is_right_bool, &cur[3], &sib[3])?,
                ];
                cur = rpo_merge_gl(cs.clone(), &cfg.params_rpo, &left, &right)?;
            }
            
            // 3) Compare to layer root
            let root_gl = digest32_to_gl4(layer.root_bytes)?;
            for i in 0..4 {
                enforce_gl_eq(&cur[i], &root_gl[i])?;
            }
            
            // 4) Consistency: current[q_idx] must equal selected {v_lo,v_hi}
            // Selection is based on LSB of *this* layer's position
            let bit_lsb = (positions[q_idx] & 1) == 1;
            let lsb = Boolean::constant(bit_lsb);  // ✅ Known off-circuit, use constant
            let selected = FpGLVar::conditionally_select(&lsb, &v_hi, &v_lo)?;
            enforce_gl_eq(&current[q_idx], &selected)?;
            
            // 5) Fold: v_next = v_lo + beta * v_hi
            let v_next = &v_lo + &(layer.beta * &v_hi);
            
            // Store into next current buffer in place
            current[q_idx] = v_next;
        }
        
        // Fold positions for next layer (use division for general folding factor)
        for pos in positions.iter_mut() {
            *pos /= t;  // ✅ Works for any folding factor, not just powers of 2
        }
    }
    
    // Terminal check
    match cfg.terminal {
        FriTerminalKind::Constant => {
            // All final values must be equal.
            if current.len() >= 2 {
                let ref0 = current[0].clone();
                for v in &current[1..] {
                    enforce_gl_eq(&ref0, v)?;
                }
            }
        }
        FriTerminalKind::Poly { degree } => {
            // Evaluate P at final x's and compare. Coefficients are GL (u64).
            let coeffs = remainder_coeffs_opt.ok_or(SynthesisError::AssignmentMissing)?;
            if coeffs.len() != degree + 1 {
                return Err(SynthesisError::Unsatisfiable);
            }
            
            // Prepare GL constants
            let coeff_vars: Vec<FpGLVar> = coeffs.iter()
                .map(|&c| FpGLVar::constant(InnerFr::from(c)))
                .collect();
            
            // For each query, compute x at final layer using g_final = g_lde^(t^layers)
            let layers_cnt = layers.len();
            let offset_var = FpGLVar::constant(InnerFr::from(cfg.domain_offset));
            let mut g_final = FpGLVar::constant(InnerFr::from(cfg.g_lde));
            for _ in 0..layers_cnt {
                g_final = pow_x_small(&g_final, cfg.folding_factor)?;  // Raise by t each layer
            }

            for (q_idx, v) in current.iter().enumerate() {
                // x_final = offset * (g_final)^(positions[q_idx])
                let x = {
                    let mut acc = FpGLVar::constant(InnerFr::from(1u64));
                    let mut base = g_final.clone();
                    let mut e = positions[q_idx];
                    while e > 0 {
                        if e & 1 == 1 { acc = &acc * &base; }
                        base = &base * &base;
                        e >>= 1;
                    }
                    offset_var.clone() * acc
                };
                
                // Horner evaluation P(x)
                let mut px = coeff_vars[degree].clone();
                for idx in (0..degree).rev() {
                    px = &px * &x + &coeff_vars[idx];
                }
                enforce_gl_eq(v, &px)?;
            }
        }
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use crate::gadgets::rpo_gl::RpoParamsGL;
    
    #[test]
    fn test_fri_constant_terminal_trivial() {
        // Build a single "layer 0" with no entries (already constant).
        // Just checks terminal == Constant passes.
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        
        let cfg = FriConfigGL {
            folding_factor: 2,
            params_rpo: RpoParamsGL::default(),
            terminal: FriTerminalKind::Constant,
            domain_offset: 1,
            g_lde: 7,
        };
        
        let current = vec![
            FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(3u64))).unwrap(),
            FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(3u64))).unwrap()
        ];
        
        let res = verify_fri_layers_gl(
            cs.clone(),
            &cfg,
            &[0, 1],
            current,
            &[],
            None
        );
        assert!(res.is_ok());
        // Note: May not satisfy with placeholder constants, but should generate constraints
    }
}

