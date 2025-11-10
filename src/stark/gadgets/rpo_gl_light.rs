//! Light RPO-256: Congruence-only Goldilocks Operations
//!
//! This module implements Winterfell's Rp64_256 hasher using congruence-based
//! Goldilocks arithmetic without per-operation canonicalization.
//!
//! ## Architecture
//!
//! The implementation uses "light" operations that enforce modular congruence
//! rather than canonical representation:
//! - Inside permutation: Pure congruence checks (a·b = r + q·p_GL)
//! - At boundaries: Canonicalize to bytes when comparing to proof commitments
//!
//! ## Constraint Complexity
//!
//! - Light permutation: approximately 7,812 constraints
//! - Comparison baseline: approximately 293,271 constraints with per-step canonicalization
//!
//! ## Security Model
//!
//! Non-linear operations (multiplication, inversion, S-box) enforce modular congruence:
//! ```text
//! a·b - result = quotient·p_GL    (quotient is unconstrained witness)
//! ```
//!
//! Canonicalization occurs only at serialization boundaries:
//! - Merkle roots (trace, composition, FRI layers)
//! - OOD frame commitment  
//! - Any digest compared to proof bytes
//!

use super::gl_fast::{gl_add_light, gl_mul_light, GlVar};
use crate::outer_compressed::InnerFr;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::uint64::UInt64 as UInt64Var;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

type UInt64GLVar = UInt64Var<InnerFr>;

pub type FpGLVar = FpVar<InnerFr>;

/// RPO-256 parameters for Goldilocks field
#[derive(Clone)]
pub struct RpoParamsGLLight {
    pub rounds: usize,
    pub width: usize,
    pub ark1: Vec<Vec<u64>>, // Round constants (first half)
    pub ark2: Vec<Vec<u64>>, // Round constants (second half)
    pub mds: Vec<Vec<u64>>,  // MDS matrix
}

impl Default for RpoParamsGLLight {
    fn default() -> Self {
        // Extract actual Winterfell Rp64_256 constants
        use winter_crypto::hashers::Rp64_256;

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
            rounds: Rp64_256::NUM_ROUNDS, // 7
            width: Rp64_256::STATE_WIDTH, // 12
            ark1,
            ark2,
            mds,
        }
    }
}

/// Apply S-box: x^7 using light GL operations
fn apply_sbox_light(cs: ConstraintSystemRef<InnerFr>, x: &GlVar) -> Result<GlVar, SynthesisError> {
    // x^7 = x * x^2 * x^4
    let x2 = gl_mul_light(cs.clone(), x, x)?; // x^2
    let x4 = gl_mul_light(cs.clone(), &x2, &x2)?; // x^4
    let x3 = gl_mul_light(cs.clone(), &x2, x)?; // x^3 = x^2 * x
    let x7 = gl_mul_light(cs.clone(), &x4, &x3)?; // x^7 = x^4 * x^3
    Ok(x7)
}

/// Apply inverse S-box: x^(1/7) using light GL operations
fn apply_inv_sbox_light(
    cs: ConstraintSystemRef<InnerFr>,
    y: &GlVar,
) -> Result<GlVar, SynthesisError> {
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_inv_sbox};

    // Witness the inverse
    let y_val = fr_to_gl_u64(y.0.value().unwrap_or_default());
    let x_val = gl_inv_sbox(y_val);
    let x = GlVar(FpVar::new_witness(cs.clone(), || {
        Ok(InnerFr::from(x_val as u128))
    })?);

    // Verify: x^7 = y (this enforces the modular congruence)
    let x7 = apply_sbox_light(cs, &x)?;
    x7.0.enforce_equal(&y.0)?;

    Ok(x)
}

/// Apply MDS matrix multiplication using light GL operations
fn apply_mds_light(
    cs: ConstraintSystemRef<InnerFr>,
    state: &mut [GlVar],
    mds: &[Vec<u64>],
) -> Result<(), SynthesisError> {
    let mut new_state = vec![GlVar(FpVar::constant(InnerFr::from(0u64))); state.len()];

    for i in 0..state.len() {
        for j in 0..state.len() {
            // new_state[i] += mds[i][j] * state[j]
            let mds_const = GlVar(FpVar::constant(InnerFr::from(mds[i][j] as u128)));
            let prod = gl_mul_light(cs.clone(), &mds_const, &state[j])?;
            new_state[i] = gl_add_light(cs.clone(), &new_state[i], &prod)?;
        }
    }

    // Copy back
    state.clone_from_slice(&new_state);
    Ok(())
}

/// Apply one round of RPO permutation using light GL operations
/// Winterfell structure: α → MDS → ARK1 → α⁻¹ → MDS → ARK2
/// NOTE: Both α and α⁻¹ are applied to ALL 12 elements!
fn apply_round_light(
    cs: ConstraintSystemRef<InnerFr>,
    state: &mut [GlVar],
    ark1: &[u64],
    ark2: &[u64],
    mds: &[Vec<u64>],
) -> Result<(), SynthesisError> {
    // Step 1: Apply forward S-boxes (x^7) to ALL elements
    for i in 0..state.len() {
        state[i] = apply_sbox_light(cs.clone(), &state[i])?;
    }

    // Step 2: Apply MDS
    apply_mds_light(cs.clone(), state, mds)?;

    // Step 3: Add ARK1 constants
    for i in 0..state.len() {
        let rc = GlVar(FpVar::constant(InnerFr::from(ark1[i] as u128)));
        state[i] = gl_add_light(cs.clone(), &state[i], &rc)?;
    }

    // Step 4: Apply inverse S-boxes (x^(1/7)) to ALL elements
    for i in 0..state.len() {
        state[i] = apply_inv_sbox_light(cs.clone(), &state[i])?;
    }

    // Step 5: Apply MDS again
    apply_mds_light(cs.clone(), state, mds)?;

    // Step 6: Add ARK2 constants
    for i in 0..state.len() {
        let rc = GlVar(FpVar::constant(InnerFr::from(ark2[i] as u128)));
        state[i] = gl_add_light(cs.clone(), &state[i], &rc)?;
    }

    Ok(())
}

/// Light RPO-256 permutation
pub fn rpo256_permute_light(
    cs: ConstraintSystemRef<InnerFr>,
    input: &[GlVar], // 12 GL elements
    params: &RpoParamsGLLight,
) -> Result<Vec<GlVar>, SynthesisError> {
    assert_eq!(input.len(), params.width, "Input must be width 12");

    let mut state = input.to_vec();

    // Apply all rounds (Winterfell RPO: α → MDS → ARK1 → α⁻¹ → MDS → ARK2)
    for round_idx in 0..params.rounds {
        apply_round_light(
            cs.clone(),
            &mut state,
            &params.ark1[round_idx],
            &params.ark2[round_idx],
            &params.mds,
        )?;
    }

    Ok(state)
}

/// Canonicalize GL values to bytes ONLY at serialization boundaries
pub fn canonicalize_to_bytes(
    cs: ConstraintSystemRef<InnerFr>,
    gl_values: &[GlVar], // 4 GL values for 32 bytes
) -> Result<Vec<UInt8<InnerFr>>, SynthesisError> {
    use super::gl_range::gl_alloc_u64;

    let mut bytes = Vec::with_capacity(32);

    for gl_val in gl_values {
        // Witness the canonical u64 value
        use crate::stark::gl_u64::fr_to_gl_u64;
        let canonical_u64 = fr_to_gl_u64(gl_val.0.value().unwrap_or_default());

        // Allocate with range check to ensure < 2^64
        let (u64_var, canonical_fp) = gl_alloc_u64(cs.clone(), Some(canonical_u64))?;

        // Enforce: gl_val ≡ canonical_fp (mod p_GL) with BOUNDED quotient
        // Use enforce_gl_eq_with_bound(q ≤ 1) for soundness
        use crate::stark::inner_stark_full::enforce_gl_eq_with_bound;
        enforce_gl_eq_with_bound(&gl_val.0, &canonical_fp, Some(1))?;

        // Convert u64 to bytes
        let bytes_8 = u64_var.to_bytes_le()?;
        bytes.extend_from_slice(&bytes_8);
    }

    Ok(bytes)
}

/// Canonicalize a single GL element to UInt64 and enforce modular congruence with bounded quotient.
pub fn canonicalize_gl_to_u64_light(
    cs: ConstraintSystemRef<InnerFr>,
    gl_val: &GlVar,
) -> Result<UInt64GLVar, SynthesisError> {
    use super::gl_range::gl_alloc_u64;
    use crate::stark::inner_stark_full::enforce_gl_eq_with_bound;
    use crate::stark::gl_u64::fr_to_gl_u64;
    let canonical_u64 = fr_to_gl_u64(gl_val.0.value().unwrap_or_default());
    let (u64_var, canonical_fp) = gl_alloc_u64(cs.clone(), Some(canonical_u64))?;
    enforce_gl_eq_with_bound(&gl_val.0, &canonical_fp, Some(1))?;
    Ok(u64_var)
}
/// Hash elements using light RPO (matches Winterfell's hash_elements)
/// State layout: [len, 0, 0, 0, input..., padding]
/// Digest output: state[4..8]
pub fn rpo_hash_elements_light(
    cs: ConstraintSystemRef<InnerFr>,
    elems: &[GlVar],
    params: &RpoParamsGLLight,
) -> Result<Vec<GlVar>, SynthesisError> {
    // Initialize state to zeros
    let mut state: Vec<GlVar> = (0..12)
        .map(|_| GlVar(FpVar::constant(InnerFr::from(0u64))))
        .collect();

    // state[0] = input length (Winterfell stores total length)
    let len = elems.len() as u64;
    state[0] = GlVar(FpVar::constant(InnerFr::from(len as u128)));

    // Absorb elements into rate portion (state[4..12])
    let mut i = 0;
    for elem in elems.iter() {
        // Add element to state[4 + i]
        state[4 + i] = gl_add_light(cs.clone(), &state[4 + i], elem)?;
        i += 1;

        // If we've filled 8 rate elements, permute
        if i == 8 {
            state = rpo256_permute_light(cs.clone(), &state, params)?;
            i = 0; // Reset for next block
        }
    }

    // If there are remaining elements (partial block), permute once more
    if i > 0 {
        state = rpo256_permute_light(cs.clone(), &state, params)?;
    }

    // Return digest from state[4..8]
    Ok(state[4..8].to_vec())
}

/// Merge two digests using light RPO (matches Winterfell's merge)
pub fn rpo_merge_light(
    cs: ConstraintSystemRef<InnerFr>,
    left: &[GlVar],  // 4 GL elements
    right: &[GlVar], // 4 GL elements
    params: &RpoParamsGLLight,
) -> Result<Vec<GlVar>, SynthesisError> {
    assert_eq!(left.len(), 4, "Left digest must be 4 elements");
    assert_eq!(right.len(), 4, "Right digest must be 4 elements");

    // Merge is just hash of concatenated digests
    let mut input = Vec::with_capacity(8);
    input.extend_from_slice(left);
    input.extend_from_slice(right);

    rpo_hash_elements_light(cs, &input, params)
}

/// Merge digest with integer counter (matches Winterfell's merge_with_int)
/// Used in counter-based PRNG: hash(digest || counter)
pub fn rpo_merge_with_int_light(
    cs: ConstraintSystemRef<InnerFr>,
    digest: &[GlVar], // 4 GL elements
    counter: u64,
    params: &RpoParamsGLLight,
) -> Result<Vec<GlVar>, SynthesisError> {
    assert_eq!(digest.len(), 4, "Digest must be 4 elements");

    // Convert counter to GL element
    let counter_gl = GlVar(FpVar::constant(InnerFr::from(counter as u128)));

    // Merge is hash(digest || counter)
    let mut input = Vec::with_capacity(5);
    input.extend_from_slice(digest);
    input.push(counter_gl);

    rpo_hash_elements_light(cs, &input, params)
}

/// Hash two child nodes to get parent using light RPO
/// This is an alias for rpo_merge_light for Merkle tree use
pub fn hash_merkle_nodes_light(
    cs: ConstraintSystemRef<InnerFr>,
    left: &[GlVar],  // 4 GL elements
    right: &[GlVar], // 4 GL elements
    params: &RpoParamsGLLight,
) -> Result<Vec<GlVar>, SynthesisError> {
    rpo_merge_light(cs, left, right, params)
}

/// Light RPO sponge for incremental absorption (stateful API like Rpo256GlVar)
pub struct Rpo256GlVarLight {
    cs: ConstraintSystemRef<InnerFr>,
    pub params: RpoParamsGLLight,
    pub state: Vec<GlVar>,
    pub rate_idx: usize, // next absorb slot (0..7)
}

impl Rpo256GlVarLight {
    pub fn new(
        cs: ConstraintSystemRef<InnerFr>,
        params: RpoParamsGLLight,
    ) -> Result<Self, SynthesisError> {
        // Initialize state to zeros
        let state = (0..12)
            .map(|_| GlVar(FpVar::constant(InnerFr::from(0u64))))
            .collect();

        Ok(Self {
            cs,
            params,
            state,
            rate_idx: 0,
        })
    }

    /// Absorb elements into the sponge (rate portion starts at index 4)
    pub fn absorb(&mut self, elems: &[GlVar]) -> Result<(), SynthesisError> {
        let rate_base = 4; // Rate starts at lane 4 in Rp64_256

        for elem in elems {
            if self.rate_idx == 8 {
                // Rate full, permute before continuing
                self.permute()?;
                self.rate_idx = 0;
            }

            // Add element to state[rate_base + rate_idx]
            self.state[rate_base + self.rate_idx] = gl_add_light(
                self.cs.clone(),
                &self.state[rate_base + self.rate_idx],
                elem,
            )?;
            self.rate_idx += 1;
        }

        Ok(())
    }

    /// Apply the RPO permutation to current state
    pub fn permute(&mut self) -> Result<(), SynthesisError> {
        self.state = rpo256_permute_light(self.cs.clone(), &self.state, &self.params)?;
        Ok(())
    }

    /// Squeeze n field elements from the sponge
    pub fn squeeze(&mut self, n: usize) -> Result<Vec<GlVar>, SynthesisError> {
        let mut output = Vec::with_capacity(n);

        while output.len() < n {
            self.permute()?;

            // Extract from digest lanes [4..8)
            for i in 4..8 {
                if output.len() == n {
                    break;
                }
                output.push(self.state[i].clone());
            }
        }

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_light_rpo_constraints() {
        let cs = ConstraintSystem::<InnerFr>::new_ref();

        // Create test input
        let input: Vec<GlVar> = (0..12)
            .map(|i| {
                GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(i as u128))).unwrap())
            })
            .collect();

        let params = RpoParamsGLLight::default();

        let start = cs.num_constraints();
        rpo256_permute_light(cs.clone(), &input, &params).unwrap();
        let permute_constraints = cs.num_constraints() - start;

        assert!(permute_constraints < 15000, "Should be <15k constraints");

        // Test canonicalization
        let gl_values: Vec<GlVar> = (0..4)
            .map(|i| {
                GlVar(
                    FpVar::new_witness(cs.clone(), || {
                        Ok(InnerFr::from((12345678901234567u64 + i) as u128))
                    })
                    .unwrap(),
                )
            })
            .collect();

        canonicalize_to_bytes(cs.clone(), &gl_values).unwrap();

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints should be satisfied"
        );
    }
}

// COUNTER-BASED RANDOM COIN (matches Winterfell's DefaultRandomCoin)
// ================================================================================================

/// Counter-based RandomCoin gadget matching Winterfell's DefaultRandomCoin
/// Uses hash(seed || counter) for each draw instead of sponge squeeze
pub struct RandomCoinGL {
    cs: ConstraintSystemRef<InnerFr>,
    pub params: RpoParamsGLLight,
    pub seed: Vec<GlVar>, // Current seed (4 GL elements)
    pub counter: u64,     // Draw counter
}

impl RandomCoinGL {
    /// Create new RandomCoin by hashing the initial seed elements
    pub fn new(
        cs: ConstraintSystemRef<InnerFr>,
        seed_elems: &[GlVar],
        params: RpoParamsGLLight,
    ) -> Result<Self, SynthesisError> {
        // seed = hash(seed_elems)
        let seed = rpo_hash_elements_light(cs.clone(), seed_elems, &params)?;

        Ok(RandomCoinGL {
            cs,
            params,
            seed,
            counter: 0,
        })
    }

    /// Reseed the coin: new_seed = merge(current_seed, data), counter = 0
    pub fn reseed(&mut self, data: &[GlVar]) -> Result<(), SynthesisError> {
        assert_eq!(data.len(), 4, "Reseed data must be 4 GL elements (digest)");
        self.seed = rpo_merge_light(self.cs.clone(), &self.seed, data, &self.params)?;
        self.counter = 0;
        Ok(())
    }

    /// Reseed the coin with a public nonce (matches merge_with_int) and enforce grinding factor.
    pub fn reseed_with_nonce(
        &mut self,
        nonce: u64,
        grinding_factor: usize,
    ) -> Result<(), SynthesisError> {
        if grinding_factor > 64 {
            return Err(SynthesisError::Unsatisfiable);
        }

        let new_seed = rpo_merge_with_int_light(self.cs.clone(), &self.seed, nonce, &self.params)?;
        // Enforce grinding on first limb only (matches DefaultRandomCoin::check_leading_zeros)
        if grinding_factor > 0 {
            let u64_limb = canonicalize_gl_to_u64_light(self.cs.clone(), &new_seed[0])?;
            let bits = u64_limb.to_bits_le()?;
            for i in 0..grinding_factor {
                bits[i].enforce_equal(&Boolean::constant(false))?;
            }
        }

        self.seed = new_seed;
        self.counter = 0;
        Ok(())
    }

    /// Draw next random GL element: hash(seed || ++counter)
    pub fn draw(&mut self) -> Result<GlVar, SynthesisError> {
        self.counter += 1;
        let digest =
            rpo_merge_with_int_light(self.cs.clone(), &self.seed, self.counter, &self.params)?;
        // Return first element of digest as the random value
        Ok(digest[0].clone())
    }

    /// Draw next pseudo-random integer limited to domain_bits (power-of-two domain)
    pub fn draw_integer_masked(
        &mut self,
        domain_bits: usize,
    ) -> Result<UInt64GLVar, SynthesisError> {
        if domain_bits > 64 {
            return Err(SynthesisError::Unsatisfiable);
        }
        self.counter += 1;
        let digest =
            rpo_merge_with_int_light(self.cs.clone(), &self.seed, self.counter, &self.params)?;
        // Use only first digest limb; canonicalize to u64 and mask high bits (no constraints on discarded bits)
        let u64_full = canonicalize_gl_to_u64_light(self.cs.clone(), &digest[0])?;
        let bits_full = u64_full.to_bits_le()?;
        let mut masked_bits = Vec::with_capacity(64);
        for i in 0..64 {
            if i < domain_bits {
                masked_bits.push(bits_full[i].clone());
            } else {
                masked_bits.push(Boolean::constant(false));
            }
        }
        Ok(UInt64GLVar::from_bits_le(&masked_bits))
    }
}
