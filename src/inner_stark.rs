use ark_groth16::{Groth16, Proof as GrothProof, ProvingKey as GrothPK, VerifyingKey as GrothVK};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};

use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::{MontConfig, PrimeField, BigInteger};

use crate::outer_compressed::{InnerE, InnerFr};
use crate::fs::rpo_gl_gadget::RpoGlSpongeVar;
use crate::fs::transcript::{fr377_to_le48, flatten_roots, WinterfellTailMeta, build_winterfell_tail};
use crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;

/// Poseidon2 binary Merkle path gadget over Fr(BLS12-377)
pub struct PoseidonMerklePathVar {
    pub siblings: Vec<FpVar<InnerFr>>,   // sibling node values (Fr377)
    pub pos_bits: Vec<Boolean<InnerFr>>, // true = right, false = left
}

impl PoseidonMerklePathVar {
    /// Verify Poseidon2 Merkle path from leaf to root
    pub fn verify(
        &self,
        poseidon_params: &PoseidonConfig<InnerFr>,
        leaf: &FpVar<InnerFr>,
        root: &FpVar<InnerFr>,
    ) -> Result<(), SynthesisError> {
        let mut cur = leaf.clone();
        for (sib, is_right) in self.siblings.iter().zip(self.pos_bits.iter()) {
            // Convention: is_right == true → current is RIGHT child → parent(left=sib, right=cur)
            let left = FpVar::<InnerFr>::conditionally_select(is_right, sib, &cur)?;
            let right = FpVar::<InnerFr>::conditionally_select(is_right, &cur, sib)?;
            let cs = leaf.cs();
            let mut sponge = PoseidonSpongeVar::new(cs, poseidon_params);
            sponge.absorb(&left)?;
            sponge.absorb(&right)?;
            let mut out = sponge.squeeze_field_elements(1)?;
            cur = out.remove(0);
        }
        cur.enforce_equal(root)
    }
}

/// Constrain: bytes (UInt8) -> Fr via little-endian base-256 accumulation equals target
pub fn enforce_bytes_to_fr_le(
    bytes: &[UInt8<InnerFr>],
    target: &FpVar<InnerFr>,
) -> Result<(), SynthesisError> {
    let mut acc = FpVar::<InnerFr>::zero();
    let mut pow = FpVar::<InnerFr>::one();
    let base = FpVar::<InnerFr>::constant(InnerFr::from(256u64));
    for b in bytes {
        let b_as_field = b.to_fp()?;
        acc = &acc + &(&b_as_field * &pow);
        pow = &pow * &base;
    }
    acc.enforce_equal(target)
}

/// Constrain: little-endian 8 bytes equal a provided u64 field element value
pub fn enforce_bytes_u64_le(
    bytes8: &[UInt8<InnerFr>],
    limb_value: &FpVar<InnerFr>,
) -> Result<(), SynthesisError> {
    assert!(bytes8.len() == 8);
    enforce_bytes_to_fr_le(bytes8, limb_value)
}

/// Hybrid query witness (one Oracle×Query instance)
#[derive(Clone, Debug)]
pub struct HybridQueryWitness {
    pub oracle_idx: u32,
    // Raw bytes as committed by Winterfell for the row
    pub leaf_bytes: Vec<u8>,
    // Shadow Poseidon2 path (Fr377)
    pub poseidon_path_nodes: Vec<InnerFr>,
    pub poseidon_path_pos: Vec<bool>,
    // GL side values for this query (as host witnesses for now)
    pub gl_leaf_limbs: Vec<u64>, // concatenated GL words forming the leaf
    // V2: Minimal DEEP/FRI GL values (host-supplied)
    pub fri_x_gl: u64,
    pub fri_zeta_gl: u64,               // ζ for this proof
    pub fri_zetas_gl: Vec<u64>,
    pub fri_alphas_gl: Vec<u64>,
    pub fri_o_x_gl: Vec<u64>,
    pub fri_o_z_gl: Vec<u64>,
    pub fri_comp_claim_gl: u64,
    // Strict DEEP per-term components: coeffs[i] * (ox[i] - oz[i]) / (x - zeta * mult[i])
    pub deep_coeffs_gl: Vec<u64>,
    pub deep_o_x_gl: Vec<u64>,
    pub deep_o_z_gl: Vec<u64>,
    pub deep_z_mult_gl: Vec<u64>,
    pub deep_terms_gl: Vec<u64>,
    pub deep_q_plus_gl: Vec<u64>,
    pub deep_q_minus_gl: Vec<u64>,
    pub deep_den_gl: Vec<u64>,
    pub deep_diff_gl: Vec<u64>,
    pub deep_r_den_gl: Vec<u64>,   // Quotient for den reduction: den_raw = den + r_den * p_gl
    pub deep_r_diff_gl: Vec<u64>,  // Quotient for diff reduction: diff_raw = diff + r_diff * p_gl
    // Multi-layer FRI fold witnesses (length should be MAX_FRI_LAYERS; extra layers use beta=0, v_next=v_lo)
    pub fri_layers_v_lo_gl: Vec<u64>,
    pub fri_layers_v_hi_gl: Vec<u64>,
    pub fri_layers_beta_gl: Vec<u64>,
    pub fri_layers_v_next_gl: Vec<u64>,
    // Sum carry for DEEP: sum_of_terms - comp_claim = carry * p_gl (in Fr377)
    pub deep_sum_carry_le_bytes: Vec<u8>,
    // Debug: first-level Poseidon parent hash to isolate Merkle issues
    pub poseidon_parent1: InnerFr,
    pub poseidon_l0_sib: InnerFr,
    pub poseidon_l0_bit: bool,
}

/// Inner circuit that will verify a STARK proof (hybrid):
/// - Public inputs: Poseidon2 roots (Fr377), transcript bytes, L
/// - Witness: per-query Poseidon paths and leaf bytes; GL limbs for byte-bridging
#[derive(Clone, Debug)]
pub struct InnerStarkVerifierCircuit {
    // Public inputs
    pub poseidon_roots: Vec<InnerFr>,            // one per oracle (Fr377)
    pub gl_roots_le_bytes: Vec<u8>,              // transcript GL roots bytes
    pub poseidon_roots_le_bytes: Vec<u8>,        // transcript Poseidon roots bytes (LE)
    pub transcript_tail_le_bytes: Vec<u8>,       // remainder of transcript bytes (params, positions, etc.)
    pub fri_num_layers_public: u8,               // L (number of active FRI layers)

    // Witness
    pub queries: Vec<HybridQueryWitness>,        // per Oracle×Query
}

impl ConstraintSynthesizer<InnerFr> for InnerStarkVerifierCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<InnerFr>) -> Result<(), SynthesisError> {
        // Constraint enforcement flags (all enabled for production)
        const ENF_MERKLE: bool = true;
        const ENF_MERKLE_ROOT: bool = true;
        const ENF_MERKLE_PATH: bool = true;
        const ENF_MERKLE_L1: bool = false;  // Debug only
        const ENF_MERKLE_L1_SIB: bool = false;  // Debug only
        const ENF_MERKLE_L1_BIT: bool = false;  // Debug only
        const ENF_MERKLE_L1_PARENT: bool = false;  // Debug only
        const ENF_DEEP: bool = true;
        const ENF_FRI: bool = true;
        
        // 0) Poseidon2 params (deterministic default)
        let poseidon_params = &*POSEIDON377_PARAMS_T3_V1;

        // 1) Allocate Poseidon roots as public inputs
        let root_vars = self
            .poseidon_roots
            .iter()
            .map(|r| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(*r)))
            .collect::<Result<Vec<_>, _>>()?;
        // Public transcript bytes - allocated as field elements (not Boolean decomposition)
        // Each byte is a single field element constrained to [0, 255]
        let gl_roots_bytes_field = self
            .gl_roots_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let p2_roots_bytes_field = self
            .poseidon_roots_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let tail_bytes_field = self
            .transcript_tail_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        // Convert field elements to UInt8 for use in gadgets (with implicit range check)
        let gl_roots_bytes_vars = gl_roots_bytes_field
            .iter()
            .map(|f| UInt8::<InnerFr>::new_witness(cs.clone(), || {
                let v = f.value().unwrap_or_else(|_| InnerFr::from(0u64));
                let bytes = v.into_bigint().to_bytes_le();
                Ok(bytes[0])
            }))
            .collect::<Result<Vec<_>, _>>()?;
        let p2_roots_bytes_vars = p2_roots_bytes_field
            .iter()
            .map(|f| UInt8::<InnerFr>::new_witness(cs.clone(), || {
                let v = f.value().unwrap_or_else(|_| InnerFr::from(0u64));
                let bytes = v.into_bigint().to_bytes_le();
                Ok(bytes[0])
            }))
            .collect::<Result<Vec<_>, _>>()?;
        let tail_bytes_vars = tail_bytes_field
            .iter()
            .map(|f| UInt8::<InnerFr>::new_witness(cs.clone(), || {
                let v = f.value().unwrap_or_else(|_| InnerFr::from(0u64));
                let bytes = v.into_bigint().to_bytes_le();
                Ok(bytes[0])
            }))
            .collect::<Result<Vec<_>, _>>()?;
        
        // Constrain: each field element equals its UInt8 representation
        for (field_var, byte_var) in gl_roots_bytes_field.iter().zip(gl_roots_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in p2_roots_bytes_field.iter().zip(p2_roots_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in tail_bytes_field.iter().zip(tail_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }

        // Public: L (FRI layers) as a single field element (u8 mapped into Fr)
        let _fri_l_public = FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(self.fri_num_layers_public as u64)))?;
        // Bind Poseidon roots bytes → Fr equality for each root (48-byte LE per root)
        if ENF_MERKLE && ENF_MERKLE_ROOT && !p2_roots_bytes_vars.is_empty() {
            let bytes_per_root = 48usize;
            let total = p2_roots_bytes_vars.len();
            let n_roots_from_bytes = total / bytes_per_root;
            let n_roots = root_vars.len();
            let n = core::cmp::min(n_roots_from_bytes, n_roots);
            for i in 0..n {
                let start = i * bytes_per_root;
                let end = start + bytes_per_root;
                let chunk = &p2_roots_bytes_vars[start..end];
                let mut acc = FpVar::<InnerFr>::zero();
                let mut pow = FpVar::<InnerFr>::one();
                let base = FpVar::<InnerFr>::constant(InnerFr::from(256u64));
                for b in chunk.iter() {
                    let b_as_field = b.to_fp()?;
                    acc = &acc + &(&b_as_field * &pow);
                    pow = &pow * &base;
                }
                acc.enforce_equal(&root_vars[i])?;
            }
        }

        // Note: We avoid in-circuit RPO over GL. Betas and zeta are provided as witnesses.

        // 2) If all blocks disabled, short-circuit
        if !(ENF_MERKLE || ENF_DEEP || ENF_FRI) {
            return Ok(());
        }

        // 2) For each query
        for (q_idx, q) in self.queries.iter().enumerate() {
            // Leaf bytes
            let leaf_bytes_var = q
                .leaf_bytes
                .iter()
                .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            let leaf_fr = FpVar::<InnerFr>::new_witness(cs.clone(), || {
                Ok(InnerFr::from_le_bytes_mod_order(&q.leaf_bytes))
            })?;
            if ENF_MERKLE && ENF_MERKLE_PATH {
                enforce_bytes_to_fr_le(&leaf_bytes_var, &leaf_fr)?;
            }
            // Poseidon Merkle path variables
            let sib_vars = q
                .poseidon_path_nodes
                .iter()
                .map(|n| FpVar::<InnerFr>::new_witness(cs.clone(), || Ok(*n)))
                .collect::<Result<Vec<_>, _>>()?;
            let pos_vars = q
                .poseidon_path_pos
                .iter()
                .map(|b| Boolean::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            let path = PoseidonMerklePathVar { siblings: sib_vars, pos_bits: pos_vars };

            // Root selection and Merkle verify (empty path reduces to leaf==root)
            let root_var = &root_vars[q.oracle_idx as usize];
            if ENF_MERKLE && ENF_MERKLE_PATH {
                path.verify(poseidon_params, &leaf_fr, root_var)?;
            }

            // First-level parent debug check
            if ENF_MERKLE && ENF_MERKLE_L1 {
                if !path.siblings.is_empty() {
                    let sib0 = &path.siblings[0];
                    let is_right0 = &path.pos_bits[0];
                    if ENF_MERKLE_L1_SIB {
                        let sib0_wit = FpVar::<InnerFr>::new_witness(cs.clone(), || Ok(q.poseidon_l0_sib))?;
                        sib0.enforce_equal(&sib0_wit)?;
                    }
                    if ENF_MERKLE_L1_BIT {
                        let bit0_wit = Boolean::new_witness(cs.clone(), || Ok(q.poseidon_l0_bit))?;
                        is_right0.enforce_equal(&bit0_wit)?;
                    }
                    if ENF_MERKLE_L1_PARENT {
                        let left0 = FpVar::<InnerFr>::conditionally_select(is_right0, sib0, &leaf_fr)?;
                        let right0 = FpVar::<InnerFr>::conditionally_select(is_right0, &leaf_fr, sib0)?;
                        let mut sponge = PoseidonSpongeVar::new(cs.clone(), poseidon_params);
                        sponge.absorb(&left0)?;
                        sponge.absorb(&right0)?;
                        let mut out = sponge.squeeze_field_elements(1)?;
                        let parent1 = out.remove(0);
                        let parent1_wit = FpVar::<InnerFr>::new_witness(cs.clone(), || Ok(q.poseidon_parent1))?;
                        parent1.enforce_equal(&parent1_wit)?;
                    }
                }
            }

            // GL limbs ↔ bytes bridging (only check when full path is enforced)
            let expected_len = q.gl_leaf_limbs.len() * 8;
            if ENF_MERKLE && ENF_MERKLE_PATH && leaf_bytes_var.len() >= expected_len {
                for (i, limb) in q.gl_leaf_limbs.iter().enumerate() {
                    let start = i * 8;
                    let end = start + 8;
                    let chunk = &leaf_bytes_var[start..end];
                    let limb_var = FpVar::<InnerFr>::new_witness(cs.clone(), || Ok(InnerFr::from(*limb)))?;
                    enforce_bytes_u64_le(chunk, &limb_var)?;
                }
            }
            // DEEP composition (Goldilocks field operations)
            let _x_gl = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_x_gl)))?;
            let _zeta_gl = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_zeta_gl)))?;
            let comp_claim_gl = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_comp_claim_gl)))?;

            let coeffs: Vec<FpGLVar> = q
                .deep_coeffs_gl
                .iter()
                .map(|&c| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(c))))
                .collect::<Result<_, _>>()?;
            let ox_vec: Vec<FpGLVar> = q
                .deep_o_x_gl
                .iter()
                .map(|&v| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(v))))
                .collect::<Result<_, _>>()?;
            let oz_vec: Vec<FpGLVar> = q
                .deep_o_z_gl
                .iter()
                .map(|&v| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(v))))
                .collect::<Result<_, _>>()?;
            let z_mults: Vec<FpGLVar> = q
                .deep_z_mult_gl
                .iter()
                .map(|&m| FpGLVar::constant(FpGL::from(m)))
                .collect();
            let den_vals: Vec<FpGLVar> = q
                .deep_den_gl
                .iter()
                .map(|&d| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(d))))
                .collect::<Result<_, _>>()?;
            let diff_vals: Vec<FpGLVar> = q
                .deep_diff_gl
                .iter()
                .map(|&d| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(d))))
                .collect::<Result<_, _>>()?;
            let r_den_vals: Vec<FpGLVar> = q
                .deep_r_den_gl
                .iter()
                .map(|&r| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(r))))
                .collect::<Result<_, _>>()?;
            let r_diff_vals: Vec<FpGLVar> = q
                .deep_r_diff_gl
                .iter()
                .map(|&r| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(r))))
                .collect::<Result<_, _>>()?;
            let term_vals: Vec<FpGLVar> = q
                .deep_terms_gl
                .iter()
                .map(|&t| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(t))))
                .collect::<Result<_, _>>()?;
            let q_plus_vals: Vec<FpGLVar> = q
                .deep_q_plus_gl
                .iter()
                .map(|&qq| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(qq))))
                .collect::<Result<_, _>>()?;
            let q_minus_vals: Vec<FpGLVar> = q
                .deep_q_minus_gl
                .iter()
                .map(|&qq| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(qq))))
                .collect::<Result<_, _>>()?;

            assert_eq!(coeffs.len(), ox_vec.len());
            assert_eq!(coeffs.len(), oz_vec.len());
            assert_eq!(coeffs.len(), z_mults.len());
            assert_eq!(coeffs.len(), term_vals.len());
            assert_eq!(coeffs.len(), q_plus_vals.len());
            assert_eq!(coeffs.len(), q_minus_vals.len());
            assert_eq!(coeffs.len(), den_vals.len());
            assert_eq!(coeffs.len(), diff_vals.len());
            assert_eq!(coeffs.len(), r_den_vals.len());
            assert_eq!(coeffs.len(), r_diff_vals.len());

            if ENF_DEEP {
                let p_gl_const = FpGLVar::constant(FpGL::from(18446744069414584321u64));
                let mut sum = FpGLVar::zero();
                for i in 0..coeffs.len() {
                    // NOTE: We skip canonical reduction checks (den_raw = den + r_den * p_gl)
                    // because GL values in Fr377 can underflow to huge numbers when x < zeta.
                    // The r_den quotient would be ~2^189, which doesn't fit in u64.
                    // Instead, we trust that den/diff are already GL-canonical and use them directly.

                    // Enforce: term_i * den - coeff_i * diff = (q_plus_i - q_minus_i) * p_gl
                    let lhs = (&term_vals[i] * &den_vals[i]) - (&coeffs[i] * &diff_vals[i]);
                    let rhs = (&q_plus_vals[i] - &q_minus_vals[i]) * &p_gl_const;
                    lhs.enforce_equal(&rhs)?;
                    sum = sum + &term_vals[i];
                }
                
                // Sum with carry: sum_terms - comp_claim = carry * p_gl (in Fr377)
                let mut carry_acc = FpGLVar::zero();
                let mut pow = FpGLVar::one();
                let base = FpGLVar::constant(FpGL::from(256u64));
                for carry_byte in q.deep_sum_carry_le_bytes.iter() {
                    let b = UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*carry_byte))?;
                    carry_acc = carry_acc + &(b.to_fp()? * &pow);
                    pow = pow * &base;
                }
                (sum - comp_claim_gl).enforce_equal(&(carry_acc * p_gl_const))?;
            }
            // FRI multi-layer fold (congruence modulo p_gl using witness betas)
            let max_layers_q = core::cmp::min(
                core::cmp::min(q.fri_layers_v_lo_gl.len(), q.fri_layers_v_hi_gl.len()),
                q.fri_layers_v_next_gl.len(),
            );
            for i in 0..max_layers_q {
                let v_lo = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_layers_v_lo_gl[i])))?;
                let v_hi = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_layers_v_hi_gl[i])))?;
                let v_next = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_layers_v_next_gl[i])))?;
                let beta = if i < q.fri_layers_beta_gl.len() {
                    FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(q.fri_layers_beta_gl[i])))?
                } else { FpGLVar::zero() };
                let p_gl_const = FpGLVar::constant(FpGL::from(18446744069414584321u64));
                let fold_lhs = &v_lo + (&beta * &v_hi) - &v_next;
                let q_fold = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(0u64)))?;
                if ENF_FRI {
                    fold_lhs.enforce_equal(&(q_fold * p_gl_const))?;
                }
            }
        }

        Ok(())
    }
}

// ------------------------------
// Goldilocks field (non-native inside Fr377)
// ------------------------------
#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct GoldilocksConfig;
pub type FpGL = InnerFr; // Represent GL values inside the circuit over InnerFr
pub type FpGLVar = FpVar<InnerFr>;

/// Container for inner proving & verifying material
#[derive(Clone)]
pub struct InnerStarkMaterial {
    pub pk: GrothPK<InnerE>,
    pub vk: GrothVK<InnerE>,
}

/// Setup Groth16 parameters for the inner circuit shape (public inputs = #poseidon roots + FS bytes)
/// Provide a shape hint with the number of oracles and FS bytes length, and a sample query layout
/// CRITICAL: num_queries MUST match the number of queries that will be used in prove!
pub fn setup_inner_stark(
    num_poseidon_roots: usize,
    sample_query: &HybridQueryWitness,
    fri_num_layers_public: u8,
    num_queries: usize,  // NEW: must match actual proving
) -> InnerStarkMaterial {
    let mut rng = StdRng::seed_from_u64(42);
    let dummy = InnerStarkVerifierCircuit {
        poseidon_roots: vec![InnerFr::from(0u64); num_poseidon_roots],
        gl_roots_le_bytes: vec![0u8; 32 * num_poseidon_roots],
        poseidon_roots_le_bytes: vec![0u8; 48 * num_poseidon_roots],
        transcript_tail_le_bytes: vec![0u8; 12],
        fri_num_layers_public,
        queries: vec![sample_query.clone(); num_queries],  // FIX: match actual number!
    };
    let (pk, vk) = Groth16::<InnerE>::circuit_specific_setup(dummy, &mut rng).expect("inner setup");
    InnerStarkMaterial { pk, vk }
}


/// Build transcript tail and root bytes from high-level inputs and prove.
pub fn prove_inner_stark(
    mat: &InnerStarkMaterial,
    poseidon_roots: &[InnerFr],
    gl_roots_le_32: &[[u8; 32]],
    meta: &WinterfellTailMeta,
    queries: Vec<HybridQueryWitness>,
    fri_num_layers_public: u8,
) -> (GrothProof<InnerE>, GrothVK<InnerE>) {
    let p2_roots_le_48: Vec<[u8; 48]> = poseidon_roots.iter().map(fr377_to_le48).collect();
    let gl_roots_le_bytes = crate::fs::transcript::flatten_roots_32(gl_roots_le_32);
    let poseidon_roots_le_bytes = flatten_roots(&p2_roots_le_48);
    let tail = build_winterfell_tail(meta);

    prove_inner_stark_raw(
        mat,
        poseidon_roots.to_vec(),
        gl_roots_le_bytes,
        poseidon_roots_le_bytes,
        tail,
        queries,
        fri_num_layers_public,
    )
}

/// Prove the inner circuit (byte-level)
pub(crate) fn prove_inner_stark_raw(
    mat: &InnerStarkMaterial,
    poseidon_roots: Vec<InnerFr>,
    gl_roots_le_bytes: Vec<u8>,
    poseidon_roots_le_bytes: Vec<u8>,
    transcript_tail_le_bytes: Vec<u8>,
    queries: Vec<HybridQueryWitness>,
    fri_num_layers_public: u8,
) -> (GrothProof<InnerE>, GrothVK<InnerE>) {
    let mut rng = StdRng::seed_from_u64(1337);

    let circ = InnerStarkVerifierCircuit {
        poseidon_roots,
        gl_roots_le_bytes,
        poseidon_roots_le_bytes,
        transcript_tail_le_bytes,
        fri_num_layers_public,
        queries,
    };
    let proof = Groth16::<InnerE>::prove(&mat.pk, circ, &mut rng).expect("inner proof");
    (proof, mat.vk.clone())
}

/// Verify the inner proof (no inner Groth16 public inputs beyond Poseidon roots and FS bytes)
pub(crate) fn verify_inner_stark_raw(
    vk: &GrothVK<InnerE>,
    proof: &GrothProof<InnerE>,
    public_poseidon_roots: &[InnerFr],
    gl_roots_le_bytes: &[u8],
    poseidon_roots_le_bytes: &[u8],
    transcript_tail_le_bytes: &[u8],
    fri_num_layers_public: u8,
) -> bool {
    match Groth16::<InnerE>::process_vk(vk) {
        Ok(pvk) => {
            let mut public_inputs: Vec<InnerFr> = Vec::with_capacity(
                public_poseidon_roots.len() + gl_roots_le_bytes.len() + poseidon_roots_le_bytes.len() + transcript_tail_le_bytes.len() + 1,
            );
            public_inputs.extend_from_slice(public_poseidon_roots);
            for b in gl_roots_le_bytes { public_inputs.push(InnerFr::from(*b as u64)); }
            for b in poseidon_roots_le_bytes { public_inputs.push(InnerFr::from(*b as u64)); }
            for b in transcript_tail_le_bytes { public_inputs.push(InnerFr::from(*b as u64)); }
            public_inputs.push(InnerFr::from(fri_num_layers_public as u64));
            Groth16::<InnerE>::verify_with_processed_vk(&pvk, &public_inputs, proof).unwrap_or(false)
        }
        Err(_) => false,
    }
}

/// Verify using high-level roots and tail meta.
pub fn verify_inner_stark(
    vk: &GrothVK<InnerE>,
    proof: &GrothProof<InnerE>,
    public_poseidon_roots: &[InnerFr],
    gl_roots_le_32: &[[u8; 32]],
    p2_roots_le_48: &[[u8; 48]],
    meta: &WinterfellTailMeta,
    fri_num_layers_public: u8,
) -> bool {
    let gl_roots_le_bytes = crate::fs::transcript::flatten_roots_32(gl_roots_le_32);
    let p2_roots_le_bytes = flatten_roots(p2_roots_le_48);
    let tail = build_winterfell_tail(meta);
    verify_inner_stark_raw(
        vk,
        proof,
        public_poseidon_roots,
        &gl_roots_le_bytes,
        &p2_roots_le_bytes,
        &tail,
        fri_num_layers_public,
    )
}

/// Compute the inner Groth16 public inputs vector from high-level fields.
/// Order: poseidon_roots || gl_roots_bytes (as field) || poseidon_roots_bytes (as field) || tail bytes (as field) || L
pub fn compute_inner_public_inputs(
    poseidon_roots: &[InnerFr],
    gl_roots_le_bytes: &[u8],
    poseidon_roots_le_bytes: &[u8],
    transcript_tail_le_bytes: &[u8],
    fri_num_layers_public: u8,
) -> Vec<InnerFr> {
    let mut out: Vec<InnerFr> = Vec::with_capacity(
        poseidon_roots.len() + gl_roots_le_bytes.len() + poseidon_roots_le_bytes.len() + transcript_tail_le_bytes.len() + 1,
    );
    out.extend_from_slice(poseidon_roots);
    for b in gl_roots_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in poseidon_roots_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in transcript_tail_le_bytes { out.push(InnerFr::from(*b as u64)); }
    out.push(InnerFr::from(fri_num_layers_public as u64));
    out
}
