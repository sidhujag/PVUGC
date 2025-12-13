//! Full FRI (L>0) Layer Verification
//!
//! Implements consistency + fold + terminal check

use super::gl_fast::GlVar;
use super::gl_fast::{gl_add_light, gl_sub_light};
use super::rpo_gl_light::RpoParamsGLLight;
use crate::stark::StarkInnerFr as InnerFr;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub type FpGLVar = FpVar<InnerFr>;

#[derive(Clone, Copy, Debug)]
pub enum FriTerminalKind {
    Constant,               // final values must be all equal
    Poly { degree: usize }, // final values equal P(x) for given coeffs
}

impl FriTerminalKind {
    /// Convert to u64 for hashing (discriminant + optional data)
    pub fn to_u64(&self) -> u64 {
        match self {
            FriTerminalKind::Constant => 0,
            FriTerminalKind::Poly { degree } => 1 + (*degree as u64),
        }
    }
}

pub struct FriConfigGL {
    pub folding_factor: usize,        // typically 2
    pub params_rpo: RpoParamsGLLight, // Light RPO parameters
    pub terminal: FriTerminalKind,
    pub domain_offset: u64,     // GL element (usually 1)
    pub g_lde: u64,             // GL element: generator of LDE subgroup
    pub lde_domain_size: usize, // Size of LDE domain (trace_len * lde_blowup)
}

pub struct FriLayerQueryGL<'a> {
    pub queries: &'a [crate::stark::inner_stark_full::FriQuery], // (v_lo, v_hi, path)
    pub root_bytes: &'a [UInt8<InnerFr>],                        // layer root (32B)
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
    main_positions: &[super::gl_range::UInt64Var], // positions in initial domain (one per query)
    mut current: Vec<FpGLVar>, // DEEP sums per query
    layers: &[FriLayerQueryGL],
    remainder_coeffs_opt: Option<&[u64]>, // for Poly terminal: coeffs (low->high)
) -> Result<(), SynthesisError> {
    use crate::stark::inner_stark_full::enforce_gl_eq;
    use super::gl_range::{gl_alloc_u64, UInt64Var};

    let t = cfg.folding_factor;
    if t == 0 {
        return Err(SynthesisError::Unsatisfiable);
    }
    // Enforce binary FRI (data model uses (v_lo, v_hi))
    if cfg.folding_factor != 2 {
        return Err(SynthesisError::Unsatisfiable);
    }
    // Exact integer log2 for power-of-two sizes
    #[inline(always)]
    fn ilog2_pow2(n: usize) -> usize {
        debug_assert!(n.is_power_of_two());
        (usize::BITS - 1 - n.leading_zeros()) as usize
    }

    // Positions used for folding current evaluations across layers (unique per layer for 'current')
    let mut positions: Vec<UInt64Var> = main_positions.to_vec();
    // Full (non-unique) positions per layer (one per original query)
    let mut positions_full: Vec<UInt64Var> = main_positions.to_vec();

    // Helper: reduce a u64 position mod 2^k by masking low k bits (fixed-cost).
    fn mask_low_bits(pos: &UInt64Var, k: usize) -> Result<UInt64Var, SynthesisError> {
        let bits = pos.to_bits_le()?;
        let mut masked = Vec::with_capacity(64);
        for i in 0..64 {
            if i < k {
                masked.push(bits[i].clone());
            } else {
                masked.push(Boolean::constant(false));
            }
        }
        Ok(UInt64Var::from_bits_le(&masked))
    }

    // Track domain generator and domain size for current layer
    let mut g_current = GlVar(FpGLVar::constant(InnerFr::from(cfg.g_lde)));
    let offset = GlVar(FpGLVar::constant(InnerFr::from(cfg.domain_offset)));

    // Initial domain size is the LDE domain size
    let mut domain_size = cfg.lde_domain_size;

    for (_, layer) in layers.iter().enumerate() {
        // Fold positions for this layer: folded_pos = pos % (domain_size / folding_factor)
        let folded_domain_size = domain_size / t;
        // Domain must remain a power of two
        if folded_domain_size == 0 || (folded_domain_size & (folded_domain_size - 1)) != 0 {
            return Err(SynthesisError::Unsatisfiable);
        }
        // Derive non-unique positions for this layer from main positions
        let k_folded = ilog2_pow2(folded_domain_size);
        positions_full = positions_full
            .iter()
            .map(|pos| mask_low_bits(pos, k_folded))
            .collect::<Result<_, _>>()?;
        // Unique-vector folded positions derived from current 'positions' ordering
        let folded_positions: Vec<UInt64Var> = positions
            .iter()
            .map(|pos| mask_low_bits(pos, k_folded))
            .collect::<Result<_, _>>()?;

        // IMPORTANT (universality / fixed R1CS shape):
        // Do NOT deduplicate positions inside the circuit.
        //
        // Fiat–Shamir query collisions after folding can cause the number of unique folded
        // positions to vary across proofs. If we deduplicate here, the amount of work
        // (and thus the Groth16 R1CS shape) depends on the concrete query positions.
        //
        // We keep the per-query position vector at fixed length (= num_queries) by not
        // deduplicating. Batch Merkle verification still uses the (padded) unique openings
        // carried in the witness.
        let folded_positions_unique = folded_positions.clone();

        // Verify FRI layer commitment using batch multiproof (required)
        use super::rpo_gl_light::rpo_hash_elements_light;

        let row_length = domain_size / t;
        // Verify batch and retain Merkle-checked pairs
        if !layer.unique_indexes.is_empty()
            && !layer.batch_nodes.is_empty()
            && !layer.unique_values.is_empty()
            && layer.unique_values.len() == layer.unique_indexes.len()
        {
            // Bounds check: all indexes must be within current folded domain
            for &idx in layer.unique_indexes.iter() {
                if idx >= folded_domain_size {
                    return Err(SynthesisError::Unsatisfiable);
                }
            }
            // Build digests and retain FP pairs; zip to lock ordering with indexes.
            // NOTE: `layer.unique_*` are PER-QUERY (length == num_queries) to keep variable
            // allocation order independent of proof-specific index ordering.
            let mut leaf_digests: Vec<[GlVar; 4]> = Vec::with_capacity(layer.unique_values.len());
            let mut leaf_pairs_fp: Vec<(FpGLVar, FpGLVar)> =
                Vec::with_capacity(layer.unique_values.len());
            let mut unique_idx_vars: Vec<UInt64Var> = Vec::with_capacity(layer.unique_indexes.len());
            for (&idx, &(lo, hi)) in layer.unique_indexes.iter().zip(layer.unique_values.iter()) {
                // Allocate index as a witness u64 so it participates as a variable.
                let (idx_u64, _) = gl_alloc_u64(cs.clone(), Some(idx as u64))?;
                unique_idx_vars.push(idx_u64);
                let v_lo_fp = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(lo)))?;
                let v_hi_fp = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(hi)))?;
                let v_lo = GlVar(v_lo_fp.clone());
                let v_hi = GlVar(v_hi_fp.clone());
                let digest = rpo_hash_elements_light(cs.clone(), &[v_lo, v_hi], &cfg.params_rpo)?;
                leaf_digests.push([
                    digest[0].clone(),
                    digest[1].clone(),
                    digest[2].clone(),
                    digest[3].clone(),
                ]);
                leaf_pairs_fp.push((v_lo_fp, v_hi_fp));
            }

            // Verify batch root equals expected
            use super::merkle_batch::verify_batch_merkle_root_gl;
            verify_batch_merkle_root_gl(
                cs.clone(),
                &cfg.params_rpo,
                leaf_digests,
                &unique_idx_vars,
                &layer.batch_nodes,
                layer.batch_depth as usize,
                layer.root_bytes,
            )?;
            // Consistency: for each query slot j:
            // - enforce the Merkle opening index equals the folded position derived from pos_prev
            // - enforce `current[j]` equals the corresponding opened value (lo/hi) for that query
            for (j, pos_prev) in positions.iter().enumerate() {
                let u_j = mask_low_bits(pos_prev, k_folded)?;
                let idx_var = unique_idx_vars.get(j).ok_or(SynthesisError::Unsatisfiable)?;
                let eq = idx_var.is_eq(&u_j)?;
                eq.enforce_equal(&Boolean::constant(true))?;

                let (v_lo_fp, v_hi_fp) = leaf_pairs_fp
                    .get(j)
                    .cloned()
                    .ok_or(SynthesisError::Unsatisfiable)?;

                // Select lo/hi based on whether `pos_prev` is in the upper half of the unfolded domain.
                let pos_bits = pos_prev.to_bits_le()?;
                let half_bit_idx = ilog2_pow2(row_length);
                let sel = pos_bits.get(half_bit_idx).ok_or(SynthesisError::Unsatisfiable)?;
                let expected_value_fp =
                    FpVar::<InnerFr>::conditionally_select(sel, &v_hi_fp, &v_lo_fp)?;
                enforce_gl_eq(&current[j], &expected_value_fp)?;
            }

            // Fold to next layer using Merkle-checked pairs
            // After folding, current will have length = number of unique folded positions
            let mut next_current: Vec<FpGLVar> = Vec::with_capacity(folded_positions_unique.len());
            // Precompute pow2 table for current layer's generator: g_current^(2^k)
            let m_layer = ilog2_pow2(folded_domain_size);
            let mut pow2_g: Vec<GlVar> = Vec::with_capacity(m_layer);
            if m_layer > 0 {
                pow2_g.push(g_current.clone());
                for _ in 1..m_layer {
                    let last = pow2_g.last().unwrap().clone();
                    pow2_g.push(gl_mul_light(cs.clone(), &last, &last)?);
                }
            }
            // Batch compute denominators and invert once
            use super::gl_fast::gl_batch_inv_light;
            let two = GlVar(FpGLVar::constant(InnerFr::from(2u64)));
            let mut xes: Vec<GlVar> = Vec::with_capacity(folded_positions_unique.len());
            let mut nums: Vec<GlVar> = Vec::with_capacity(folded_positions_unique.len());
            for (j, folded_pos) in folded_positions_unique.iter().enumerate() {
                let (v_lo_fp, v_hi_fp) = leaf_pairs_fp
                    .get(j)
                    .cloned()
                    .ok_or(SynthesisError::Unsatisfiable)?;
                let v_lo_gl = GlVar(v_lo_fp);
                let v_hi_gl = GlVar(v_hi_fp);
                let beta_gl = GlVar(layer.beta.clone());
                // xe = offset * g_current^folded_pos using pow2 table
                // IMPORTANT (universality / fixed R1CS shape):
                // fixed-cost exponentiation (no variable-time loop on `folded_pos`).
                let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
                let mut acc = one_gl.clone();
                let folded_bits = folded_pos.to_bits_le()?;
                for (k, base) in pow2_g.iter().enumerate() {
                    let bit = folded_bits.get(k).ok_or(SynthesisError::Unsatisfiable)?;
                    let sel_fp = FpVar::<InnerFr>::conditionally_select(bit, &base.0, &one_gl.0)?;
                    let sel = GlVar(sel_fp);
                    acc = gl_mul_light(cs.clone(), &acc, &sel)?;
                }
                let xe = gl_mul_light(cs.clone(), &offset, &acc)?;
                xes.push(xe.clone());
                // numerator
                let beta_plus_xe = gl_add_light(cs.clone(), &beta_gl, &xe)?;
                let beta_minus_xe = gl_sub_light(cs.clone(), &beta_gl, &xe)?;
                let term1 = gl_mul_light(cs.clone(), &v_lo_gl, &beta_plus_xe)?;
                let term2 = gl_mul_light(cs.clone(), &v_hi_gl, &beta_minus_xe)?;
                let numerator = gl_sub_light(cs.clone(), &term1, &term2)?;
                nums.push(numerator);
            }
            // denominators = 2 * xe
            let mut dens: Vec<GlVar> = Vec::with_capacity(xes.len());
            for xe in &xes {
                dens.push(gl_mul_light(cs.clone(), &two, xe)?);
            }
            // batch invert
            let invs = gl_batch_inv_light(cs.clone(), &dens)?;
            // v_next = num * inv
            for i in 0..nums.len() {
                let v_next_gl = gl_mul_light(cs.clone(), &nums[i], &invs[i])?;
                next_current.push(v_next_gl.0.clone());
            }
            current = next_current;
        } else {
            return Err(SynthesisError::Unsatisfiable);
        }

        // Update domain generator for next layer: since t==2, g_current = g_current^2
        use super::gl_fast::gl_mul_light;
        g_current = gl_mul_light(cs.clone(), &g_current, &g_current)?;

        // Update domain size and positions for next layer (fixed-length per query)
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
            // IMPORTANT (universality): remainder coefficients are proof-dependent witness data.
            // Do NOT embed them as constants into the R1CS.
            let coeff_gl: Vec<GlVar> = coeffs
                .iter()
                .map(|&c| {
                    let fp = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c)))?;
                    Ok(GlVar(fp))
                })
                .collect::<Result<_, SynthesisError>>()?;

            // For each query, compute x at final layer using g_final = g_lde^(t^layers)
            let layers_cnt = layers.len();
            let offset_final = GlVar(FpGLVar::constant(InnerFr::from(cfg.domain_offset)));
            let mut g_final = GlVar(FpGLVar::constant(InnerFr::from(cfg.g_lde)));
            use super::gl_fast::{gl_add_light, gl_mul_light};
            // Since t == 2, g_final = g_lde^(2^layers_cnt) via repeated squaring
            for _ in 0..layers_cnt {
                g_final = gl_mul_light(cs.clone(), &g_final, &g_final)?;
            }
            // Precompute pow2 for g_final up to log2(final domain size)
            let final_domain = cfg.lde_domain_size / cfg.folding_factor.pow(layers_cnt as u32);
            if final_domain == 0 || (final_domain & (final_domain - 1)) != 0 {
                return Err(SynthesisError::Unsatisfiable);
            }
            let m_final = ilog2_pow2(final_domain);
            let mut pow2_final: Vec<GlVar> = Vec::with_capacity(m_final);
            if m_final > 0 {
                pow2_final.push(g_final.clone());
                for _ in 1..m_final {
                    let last = pow2_final.last().unwrap().clone();
                    pow2_final.push(gl_mul_light(cs.clone(), &last, &last)?);
                }
            }

            for (q_idx, v) in current.iter().enumerate() {
                let pos = positions.get(q_idx).ok_or(SynthesisError::Unsatisfiable)?;

                // x_final = offset_final * (g_final)^(positions[q_idx]) using GL arithmetic
                // x_final = offset_final * g_final^pos using pow2_final
                // IMPORTANT (universality / fixed R1CS shape):
                // Do a fixed amount of work independent of `pos`.
                // If we short-circuit based on `pos`'s highest set bit, the Groth16 circuit shape
                // depends on the Fiat–Shamir query positions (which vary across proofs).
                let one_gl = GlVar(FpGLVar::constant(InnerFr::from(1u64)));
                let mut acc = one_gl.clone();
        let pos_bits = pos.to_bits_le()?;
                for (k, base) in pow2_final.iter().enumerate() {
            let bit = pos_bits.get(k).ok_or(SynthesisError::Unsatisfiable)?;
            let sel_fp = FpVar::<InnerFr>::conditionally_select(bit, &base.0, &one_gl.0)?;
            let sel = GlVar(sel_fp);
            acc = gl_mul_light(cs.clone(), &acc, &sel)?;
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
            lde_domain_size: 8, // Dummy value for test
        };

        let current = vec![
            FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(3u64))).unwrap(),
            FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(3u64))).unwrap(),
        ];

        use crate::stark::gadgets::gl_range::gl_alloc_u64;
        let (p0, _) = gl_alloc_u64(cs.clone(), Some(0)).unwrap();
        let (p1, _) = gl_alloc_u64(cs.clone(), Some(1)).unwrap();
        let res = verify_fri_layers_gl(cs.clone(), &cfg, &[p0, p1], current, &[], None);
        assert!(res.is_ok());
    }
}
