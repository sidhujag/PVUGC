//! Full FRI (L>0) Layer Verification
//!
//! Implements consistency + fold + terminal check exactly as specified by expert

use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::boolean::Boolean;
use crate::outer_compressed::InnerFr;
use crate::gadgets::rpo_gl_light::RpoParamsGLLight;
use crate::gadgets::gl_fast::GlVar;
use crate::gadgets::gl_fast::{gl_add_light, gl_sub_light, gl_inv_light};

pub type FpGLVar = FpVar<InnerFr>;

#[derive(Clone, Copy, Debug)]
pub enum FriTerminalKind {
    Constant,                  // final values must be all equal
    Poly { degree: usize },    // final values equal P(x) for given coeffs
}

pub struct FriConfigGL {
    pub folding_factor: usize,         // typically 2
    pub params_rpo: RpoParamsGLLight,  // Light RPO parameters
    pub terminal: FriTerminalKind,
    pub domain_offset: u64,            // GL element (usually 1)
    pub g_lde: u64,                    // GL element: generator of LDE subgroup
    pub lde_domain_size: usize,        // Size of LDE domain (trace_len * lde_blowup)
}

pub struct FriLayerQueryGL<'a> {
    pub queries: &'a [crate::inner_stark_full::FriQuery], // (v_lo, v_hi, path)
    pub root_bytes: &'a [UInt8<InnerFr>],                 // layer root (32B)
    pub beta: &'a FpGLVar,
    // batch data for this layer
    pub unique_indexes: &'a [usize],
    pub unique_values: &'a [(u64, u64)],
    pub batch_nodes: &'a [Vec<[u8; 32]>],
    pub batch_depth: u8,
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
    
    let t = cfg.folding_factor;
    if t == 0 { return Err(SynthesisError::Unsatisfiable); }
    
    // Positions used for folding current evaluations across layers (unique per layer for 'current')
    let mut positions: Vec<usize> = main_positions.to_vec();
    // Full (non-unique) positions per layer (one per original query)
    let mut positions_full: Vec<usize> = main_positions.to_vec();
    
    // Track domain generator and domain size for current layer
    let mut g_current = GlVar(FpGLVar::constant(InnerFr::from(cfg.g_lde)));
    let offset = GlVar(FpGLVar::constant(InnerFr::from(cfg.domain_offset)));
    
    // Initial domain size is the LDE domain size
    let mut domain_size = cfg.lde_domain_size;
    
    for (_, layer) in layers.iter().enumerate() {
        
        
        // Fold positions for this layer: folded_pos = pos % (domain_size / folding_factor)
        let folded_domain_size = domain_size / t;
        // Preserve pre-fold positions (to determine hi/lo half)
        let prev_positions_full = positions_full.clone();
        // Derive non-unique positions for this layer from main positions
        positions_full = positions_full.iter().map(|&pos| pos % folded_domain_size).collect();
        // Unique-vector folded positions derived from current 'positions' ordering
        let folded_positions: Vec<usize> = positions.iter()
            .map(|&pos| pos % folded_domain_size)
            .collect();
        
        // Create deduplicated folded positions for query lookup (for 'current' folding path)
        // NOTE: Do NOT sort! Must preserve insertion order
        let mut folded_positions_unique = Vec::new();
        for &fp in &folded_positions {
            if !folded_positions_unique.contains(&fp) {
                folded_positions_unique.push(fp);
            }
        }
        
        // For each unique folded position, record the first index in this layer's (non-unique) positions providing its values
        let mut unique_first_indices: Vec<usize> = Vec::with_capacity(folded_positions_unique.len());
        for &u in &folded_positions_unique {
            let idx0 = positions_full.iter().position(|&orig_pos| orig_pos == u)
                .expect("unique element must exist in positions_full");
            unique_first_indices.push(idx0);
        }
        
        // Verify FRI layer commitment using batch multiproof (required)
        use crate::gadgets::rpo_gl_light::rpo_hash_elements_light;
        
        let row_length = domain_size / t;
        // Verify batch and retain Merkle-checked pairs
        if !layer.unique_indexes.is_empty() && !layer.batch_nodes.is_empty() && !layer.unique_values.is_empty() && layer.unique_values.len() == layer.unique_indexes.len() {
            // Build digests and retain FP pairs
            let mut leaf_digests: Vec<[GlVar; 4]> = Vec::with_capacity(layer.unique_values.len());
            let mut leaf_pairs_fp: Vec<(FpGLVar, FpGLVar)> = Vec::with_capacity(layer.unique_values.len());
            for (lo, hi) in layer.unique_values.iter() {
                let v_lo_fp = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*lo)))?;
                let v_hi_fp = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(*hi)))?;
                let v_lo = GlVar(v_lo_fp.clone());
                let v_hi = GlVar(v_hi_fp.clone());
                let digest = rpo_hash_elements_light(cs.clone(), &[v_lo, v_hi], &cfg.params_rpo)?;
                leaf_digests.push([digest[0].clone(), digest[1].clone(), digest[2].clone(), digest[3].clone()]);
                leaf_pairs_fp.push((v_lo_fp, v_hi_fp));
            }
            
            // Verify batch root equals expected
            use crate::gadgets::merkle_batch::verify_batch_merkle_root_gl;
            verify_batch_merkle_root_gl(
                cs.clone(),
                &cfg.params_rpo,
                leaf_digests,
                &layer.unique_indexes,
                &layer.batch_nodes,
                layer.batch_depth as usize,
                layer.root_bytes,
            )?;
            // Consistency: use Merkle-checked pairs in the same unique order
            for (unique_idx, &_u_pos) in folded_positions_unique.iter().enumerate() {
                let pos_idx = unique_first_indices[unique_idx];
                let (v_lo_fp, v_hi_fp) = &leaf_pairs_fp[unique_idx];
                let is_hi = prev_positions_full[pos_idx] / row_length;
                let is_lo_bool = Boolean::constant(is_hi == 0);
                let expected_value_fp = FpVar::<InnerFr>::conditionally_select(&is_lo_bool, v_lo_fp, v_hi_fp)?;
                enforce_gl_eq(&current[pos_idx], &expected_value_fp)?;
            }
            
            // Fold to next layer using Merkle-checked pairs
            // After folding, current will have length = number of unique folded positions
            let mut next_current: Vec<FpGLVar> = Vec::with_capacity(folded_positions_unique.len());
            // Precompute pow2 table for current layer's generator: g_current^(2^k)
            let m_layer = (folded_domain_size as f64).log2() as usize;
            let mut pow2_g: Vec<GlVar> = Vec::with_capacity(m_layer);
            if m_layer > 0 {
                pow2_g.push(g_current.clone());
                for _ in 1..m_layer {
                    let last = pow2_g.last().unwrap().clone();
                    pow2_g.push(gl_mul_light(cs.clone(), &last, &last)?);
                }
            }
            for (u_idx, &folded_pos) in folded_positions_unique.iter().enumerate() {
                // Use Merkle-checked pair aligned to the unique order
                let (v_lo_fp, v_hi_fp) = &leaf_pairs_fp[u_idx];
                let v_lo_gl = GlVar(v_lo_fp.clone());
                let v_hi_gl = GlVar(v_hi_fp.clone());
                let beta_gl = GlVar(layer.beta.clone());
                // xe = offset * g_current^folded_pos using pow2 table
                let mut acc = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
                let mut e = folded_pos;
                let mut k = 0usize;
                while e > 0 {
                    if (e & 1) == 1 && k < pow2_g.len() {
                        acc = gl_mul_light(cs.clone(), &acc, &pow2_g[k])?;
                    }
                    e >>= 1;
                    k += 1;
                }
                let xe = gl_mul_light(cs.clone(), &offset, &acc)?;
                // Interpolation
                let beta_plus_xe = gl_add_light(cs.clone(), &beta_gl, &xe)?;
                let beta_minus_xe = gl_sub_light(cs.clone(), &beta_gl, &xe)?;
                let term1 = gl_mul_light(cs.clone(), &v_lo_gl, &beta_plus_xe)?;
                let term2 = gl_mul_light(cs.clone(), &v_hi_gl, &beta_minus_xe)?;
                let numerator = gl_sub_light(cs.clone(), &term1, &term2)?;
                let two = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
                let denominator = gl_mul_light(cs.clone(), &two, &xe)?;
                let denom_inv = gl_inv_light(cs.clone(), &denominator)?;
                let v_next_gl = gl_mul_light(cs.clone(), &numerator, &denom_inv)?;
                next_current.push(v_next_gl.0);
            }
            current = next_current;
        } else {
            return Err(SynthesisError::Unsatisfiable);
        }
        // query_values filled via batch branch above
        
        
        
        // (Removed duplicate folding block; folding was performed with Merkle-checked pairs above)
        
        // Update domain generator for next layer: g_current = g_current^t (general folding factor)
        use crate::gadgets::gl_fast::gl_mul_light;
        let mut acc_g = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
        let mut exp = cfg.folding_factor;
        let mut base = g_current.clone();
        while exp > 0 {
            if (exp & 1) == 1 { acc_g = gl_mul_light(cs.clone(), &acc_g, &base)?; }
            exp >>= 1;
            if exp > 0 { base = gl_mul_light(cs.clone(), &base, &base)?; }
        }
        g_current = acc_g;
        
        // Update domain size and positions for next layer (unique)
        domain_size = folded_domain_size;
        positions = folded_positions_unique;
        
        
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
            
            // Prepare GL constants (coefficients are ALREADY in reverse order)
            let coeff_gl: Vec<GlVar> = coeffs.iter()
                .map(|&c| GlVar(FpGLVar::constant(InnerFr::from(c))))
                .collect();
            
            // For each query, compute x at final layer using g_final = g_lde^(t^layers)
            let layers_cnt = layers.len();
            let offset_final = GlVar(FpGLVar::constant(InnerFr::from(cfg.domain_offset)));
            let mut g_final = GlVar(FpGLVar::constant(InnerFr::from(cfg.g_lde)));
            use crate::gadgets::gl_fast::{gl_mul_light, gl_add_light};
            // Raise by folding_factor each layer (general t)
            for _ in 0..layers_cnt {
                let mut acc = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
                let mut e = cfg.folding_factor;
                let mut b = g_final.clone();
                while e > 0 {
                    if (e & 1) == 1 { acc = gl_mul_light(cs.clone(), &acc, &b)?; }
                    e >>= 1;
                    if e > 0 { b = gl_mul_light(cs.clone(), &b, &b)?; }
                }
                g_final = acc;
            }
            // Precompute pow2 for g_final up to log2(final domain size)
            let final_domain = cfg.lde_domain_size / cfg.folding_factor.pow(layers_cnt as u32);
            let m_final = (final_domain as f64).log2() as usize;
            let mut pow2_final: Vec<GlVar> = Vec::with_capacity(m_final);
            if m_final > 0 {
                pow2_final.push(g_final.clone());
                for _ in 1..m_final {
                    let last = pow2_final.last().unwrap().clone();
                    pow2_final.push(gl_mul_light(cs.clone(), &last, &last)?);
                }
            }

            for (q_idx, v) in current.iter().enumerate() {
                let pos = positions.get(q_idx).copied().unwrap_or(0);
                
                // x_final = offset_final * (g_final)^(positions[q_idx]) using GL arithmetic
                // x_final = offset_final * g_final^pos using pow2_final
                let mut acc = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
                let mut e = pos;
                let mut k = 0usize;
                while e > 0 {
                    if (e & 1) == 1 && k < pow2_final.len() {
                        acc = gl_mul_light(cs.clone(), &acc, &pow2_final[k])?;
                    }
                    e >>= 1;
                    k += 1;
                }
                let x = gl_mul_light(cs.clone(), &offset_final, &acc)?;
                
                // Evaluate P(x) using Horner's method with LIGHT operations
                let mut px = coeff_gl[0].clone();
                for idx in 1..=degree {
                    px = gl_mul_light(cs.clone(), &px, &x)?;
                    px = gl_add_light(cs.clone(), &px, &coeff_gl[idx])?;
                }
                
                // Compare using GL modular equality
                enforce_gl_eq(v, &px.0)?;
            }
        }
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    
    #[test]
    fn test_fri_constant_terminal_trivial() {
        // Build a single "layer 0" with no entries (already constant).
        // Just checks terminal == Constant passes.
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        
        let cfg = FriConfigGL {
            folding_factor: 2,
            params_rpo: RpoParamsGLLight::default(),
            terminal: FriTerminalKind::Constant,
            domain_offset: 1,
            g_lde: 7,
            lde_domain_size: 8,  // Dummy value for test
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
    }
}

