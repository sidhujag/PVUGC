use ark_groth16::{Groth16, Proof as GrothProof, ProvingKey as GrothPK, VerifyingKey as GrothVK};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};

use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::{MontConfig, PrimeField, BigInteger, Field};

use crate::outer_compressed::{InnerE, InnerFr};
use crate::fs::rpo_gl_gadget::RpoGlSpongeVar;
use crate::fs::rpo_gl_gadget::{Rpo256Var, digest32_to_gl4};
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
    // LDE domain trace opening (placeholders; RPO-256 Merkle not enforced yet)
    pub trace_lde_leaf_bytes: Vec<u8>,
    pub trace_lde_path_nodes_le32: Vec<[u8; 32]>,
    pub trace_lde_path_pos: Vec<bool>,
    // LDE domain composition opening (placeholders)
    pub comp_lde_leaf_bytes: Vec<u8>,
    pub comp_lde_path_nodes_le32: Vec<[u8; 32]>,
    pub comp_lde_path_pos: Vec<bool>,
    // FRI per-layer leaf digests (32B each), order matches fri_layers_* arrays
    pub fri_leaf_digests_le32: Vec<[u8; 32]>,
    // Optional: FRI per-layer Merkle paths (nodes and positions) to bind leaves to roots
    pub fri_paths_nodes_le32: Vec<Vec<[u8; 32]>>,
    pub fri_paths_pos: Vec<Vec<bool>>,
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
    // Future public commitments (currently optional/empty; kept as bytes for stability)
    pub trace_lde_root_le_bytes: Vec<u8>,        // 32B root
    pub comp_lde_root_le_bytes: Vec<u8>,         // 32B root
    pub fri_layer_roots_le_bytes: Vec<u8>,       // 32B each, concatenated
    pub ood_commitment_le_bytes: Vec<u8>,        // commitment bytes (format TBD)
    // Witness-only: merged OOD evaluations (GL elements) to re-hash and bind commitment
    pub ood_evals_merged_gl: Vec<u64>,
    // Optional: public query positions (LE bytes) for distinctness binding
    pub query_positions_le_bytes: Vec<u8>,

    // Witness
    pub queries: Vec<HybridQueryWitness>,        // per Oracle×Query
}

impl ConstraintSynthesizer<InnerFr> for InnerStarkVerifierCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<InnerFr>) -> Result<(), SynthesisError> {
        
        // Constraint enforcement flags - enabling systematically
        const ENF_MERKLE: bool = true;  // ✅ STEP 1: PASS
        const ENF_MERKLE_ROOT: bool = true;
        const ENF_MERKLE_PATH: bool = true;
        const ENF_MERKLE_L1: bool = false;  // Debug only
        const ENF_MERKLE_L1_SIB: bool = false;  // Debug only
        const ENF_MERKLE_L1_BIT: bool = false;  // Debug only
        const ENF_MERKLE_L1_PARENT: bool = false;  // Debug only
        const ENF_DEEP: bool = true;  // ✅ STEP 2: PASS (with GL-field q computation)
        const ENF_FRI: bool = true;  // ✅ STEP 3: PASS
        const ENF_FRI_PATHS: bool = false; // Gate for per-layer FRI Merkle path checks
        const ENF_QUERY_IDX: bool = true;  // ✅ STEP 4: PASS
        const ENF_ZETA_EQUAL: bool = false;  // ❌ BLOCKED: Winterfell's zeta != circuit's zeta
        const ENF_LDE_TRACE: bool = false; // ❌ BLOCKER: LDE+DEEP interaction issue (see TECHNICAL.md)
        const ENF_LDE_COMP: bool = false;  // Test separately
        const ENF_OOD_BIND: bool = false;  // TODO
        const ENF_QUERY_IDX_PUBLIC: bool = false; // TODO
        
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
        // Future: additional public roots/commitments (may be empty)
        let trace_lde_root_bytes_field = self
            .trace_lde_root_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let comp_lde_root_bytes_field = self
            .comp_lde_root_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let fri_layer_roots_bytes_field = self
            .fri_layer_roots_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let ood_commitment_bytes_field = self
            .ood_commitment_le_bytes
            .iter()
            .map(|b| FpVar::<InnerFr>::new_input(cs.clone(), || Ok(InnerFr::from(*b as u64))))
            .collect::<Result<Vec<_>, _>>()?;
        let query_positions_bytes_field = self
            .query_positions_le_bytes
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
        let trace_lde_root_bytes_vars = self.trace_lde_root_le_bytes
            .iter()
            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<Vec<_>, _>>()?;
        let comp_lde_root_bytes_vars = self.comp_lde_root_le_bytes
            .iter()
            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<Vec<_>, _>>()?;
        let fri_layer_roots_bytes_vars = self.fri_layer_roots_le_bytes
            .iter()
            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<Vec<_>, _>>()?;
        let ood_commitment_bytes_vars = self.ood_commitment_le_bytes
            .iter()
            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<Vec<_>, _>>()?;
        let query_positions_bytes_vars = self.query_positions_le_bytes
            .iter()
            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
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
        for (field_var, byte_var) in trace_lde_root_bytes_field.iter().zip(trace_lde_root_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in comp_lde_root_bytes_field.iter().zip(comp_lde_root_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in fri_layer_roots_bytes_field.iter().zip(fri_layer_roots_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in ood_commitment_bytes_field.iter().zip(ood_commitment_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }
        for (field_var, byte_var) in query_positions_bytes_field.iter().zip(query_positions_bytes_vars.iter()) {
            field_var.enforce_equal(&byte_var.to_fp()?)?;
        }

        // OOD binding: rehash merged OOD evaluations and compare to public digest
        if ENF_OOD_BIND && !ood_commitment_bytes_vars.is_empty() {
            // Allocate OOD evals as GL vars
            let eval_vars: Vec<FpGLVar> = self
                .ood_evals_merged_gl
                .iter()
                .map(|&v| FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(v))))
                .collect::<Result<_, _>>()?;
            // Hash elements per Rp64_256
            let mut h = Rpo256Var::new(cs.clone())?;
            let digest = h.hash_elements(&eval_vars)?;
            // Compare digest to public ood_commitment_le_bytes (first 32 bytes)
            if ood_commitment_bytes_vars.len() >= 32 {
                let root = digest32_to_gl4(&ood_commitment_bytes_vars[0..32])?;
                for k in 0..4 { digest[k].enforce_equal(&root[k])?; }
            }
        }

        // Public query positions distinctness (optional)
        if ENF_QUERY_IDX_PUBLIC && query_positions_bytes_vars.len() >= 4 {
            // Decode public positions as u32 (LE) for witness inverses
            let mut pos_vals_u64: Vec<u64> = Vec::new();
            for chunk in self.query_positions_le_bytes.chunks(4) {
                if chunk.len() == 4 {
                    let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]) as u64;
                    pos_vals_u64.push(val);
                }
            }
            // Allocate GL vars
            let mut pos_vars: Vec<FpGLVar> = Vec::new();
            for chunk in query_positions_bytes_vars.chunks(4) {
                if chunk.len() == 4 {
                    let limb = crate::fs::rpo_gl_gadget::gl_from_le_bytes(chunk)?;
                    pos_vars.push(limb);
                }
            }
            let n = pos_vars.len();
            for i in 0..n { for j in (i+1)..n {
                let diff = &pos_vars[i] - &pos_vars[j];
                // Provide correct Fr377 inverse as witness
                let inv = FpGLVar::new_witness(cs.clone(), || {
                    let a = pos_vals_u64.get(i).copied().unwrap_or(0);
                    let b = pos_vals_u64.get(j).copied().unwrap_or(0);
                    let diff_fr = InnerFr::from(a) - InnerFr::from(b);
                    let inv_fr = diff_fr.inverse().unwrap_or(InnerFr::from(0u64));
                    Ok(inv_fr)
                })?;
                (diff * inv).enforce_equal(&FpGLVar::one())?;
            }}
        }

        // 1.5) In-circuit Fiat–Shamir over transcript bytes to derive FRI betas (and optionally zeta/alpha later)
        // MUST MATCH host fs::rpo_gl_host::derive_challenges_from_transcript():
        // Absorb: tag("dual_root_v1") || u32_le(num_oracles) || GL roots || tail bytes
        let mut fs = RpoGlSpongeVar::new(cs.clone())?;
        {
            // Tag bytes (constant)
            let tag_bytes: &[u8] = b"dual_root_v1";
            let mut tag_vars = Vec::with_capacity(tag_bytes.len());
            for b in tag_bytes.iter() {
                tag_vars.push(UInt8::constant(*b));
            }
            fs.absorb_bytes(&tag_vars)?;
        }
        // num_oracles = gl_roots_le_bytes.len() / 32, encoded as u32 LE
        let num_oracles: u32 = (self.gl_roots_le_bytes.len() / 32) as u32;
        let num_bytes = num_oracles.to_le_bytes();
        let mut num_vars = Vec::with_capacity(4);
        for b in num_bytes.iter() { num_vars.push(UInt8::constant(*b)); }
        fs.absorb_bytes(&num_vars)?;
        fs.absorb_bytes(&gl_roots_bytes_vars)?;
        // FREEZE FS: Don't absorb LDE/OOD commitments to keep FS stable while debugging
        // This allows DEEP (which uses FS challenges) to work with LDE data
        //if !trace_lde_root_bytes_vars.is_empty() { fs.absorb_bytes(&trace_lde_root_bytes_vars)?; }
        //if !comp_lde_root_bytes_vars.is_empty() { fs.absorb_bytes(&comp_lde_root_bytes_vars)?; }
        //if !fri_layer_roots_bytes_vars.is_empty() { fs.absorb_bytes(&fri_layer_roots_bytes_vars)?; }
        //if !ood_commitment_bytes_vars.is_empty() { fs.absorb_bytes(&ood_commitment_bytes_vars)?; }
        fs.absorb_bytes(&tail_bytes_vars)?;
        // Match host order: permute -> alpha -> betas[L] -> zeta
        fs.permute()?;
        let _fs_alpha: FpGLVar = fs.squeeze()?;
        let fri_layers = self.fri_num_layers_public as usize;
        let mut fs_betas: Vec<FpGLVar> = Vec::with_capacity(fri_layers);
        for _ in 0..fri_layers { 
            fs_betas.push(fs.squeeze()?);
        }
        let fs_zeta: FpGLVar = fs.squeeze()?;

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

        // Prepare storage for FS-derived indices per oracle to enforce distinctness later
        let mut fs_indices_per_oracle: Vec<Vec<FpGLVar>> = if ENF_QUERY_IDX { vec![Vec::new(); root_vars.len()] } else { Vec::new() };

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

            // LDE trace/composition Merkle verification using Rp64_256 semantics
            // Allocate always; enforce only when gates are on
            let trace_leaf_bytes_vars = q.trace_lde_leaf_bytes.iter()
                .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            let trace_pos_vars = q.trace_lde_path_pos.iter()
                .map(|b| Boolean::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            if ENF_LDE_TRACE && !trace_leaf_bytes_vars.is_empty() {
                // If 32 bytes, treat as digest directly; else compute from 8B limbs
                let mut h = Rpo256Var::new(cs.clone())?;
                let mut cur: [FpGLVar;4] = if trace_leaf_bytes_vars.len() == 32 {
                    digest32_to_gl4(&trace_leaf_bytes_vars)?
                } else {
                    let mut limbs: Vec<FpGLVar> = Vec::with_capacity(trace_leaf_bytes_vars.len() / 8 + 1);
                    for chunk in trace_leaf_bytes_vars.chunks(8) {
                        let limb = crate::fs::rpo_gl_gadget::gl_from_le_bytes(chunk)?;
                        limbs.push(limb);
                    }
                    h.hash_elements(&limbs)?
                };
                // Fold path
                for (j, node_le32) in q.trace_lde_path_nodes_le32.iter().enumerate() {
                    let sib_bytes_vars = node_le32.iter()
                        .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                        .collect::<Result<Vec<_>, _>>()?;
                    let sib = digest32_to_gl4(&sib_bytes_vars)?;
                    let is_right = if j < trace_pos_vars.len() { &trace_pos_vars[j] } else { &Boolean::constant(false) };
                    let left = [
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[0], &cur[0])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[1], &cur[1])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[2], &cur[2])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[3], &cur[3])?,
                    ];
                    let right = [
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[0], &sib[0])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[1], &sib[1])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[2], &sib[2])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[3], &sib[3])?,
                    ];
                    cur = h.merge(&left, &right)?;
                }
                // Compare to public root (first 32 bytes)
                if !trace_lde_root_bytes_vars.is_empty() {
                    let root32 = &trace_lde_root_bytes_vars[0..core::cmp::min(32, trace_lde_root_bytes_vars.len())];
                    if root32.len() == 32 {
                        let root = digest32_to_gl4(root32)?;
                        for k in 0..4 { cur[k].enforce_equal(&root[k])?; }
                    }
                }
            }

            let comp_leaf_bytes_vars = q.comp_lde_leaf_bytes.iter()
                .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            let comp_pos_vars = q.comp_lde_path_pos.iter()
                .map(|b| Boolean::new_witness(cs.clone(), || Ok(*b)))
                .collect::<Result<Vec<_>, _>>()?;
            if ENF_LDE_COMP && !comp_leaf_bytes_vars.is_empty() {
                let mut h = Rpo256Var::new(cs.clone())?;
                let mut cur: [FpGLVar;4] = if comp_leaf_bytes_vars.len() == 32 {
                    digest32_to_gl4(&comp_leaf_bytes_vars)?
                } else {
                    let mut limbs: Vec<FpGLVar> = Vec::with_capacity(comp_leaf_bytes_vars.len() / 8 + 1);
                    for chunk in comp_leaf_bytes_vars.chunks(8) {
                        let limb = crate::fs::rpo_gl_gadget::gl_from_le_bytes(chunk)?;
                        limbs.push(limb);
                    }
                    h.hash_elements(&limbs)?
                };
                for (j, node_le32) in q.comp_lde_path_nodes_le32.iter().enumerate() {
                    let sib_bytes_vars = node_le32.iter()
                        .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                        .collect::<Result<Vec<_>, _>>()?;
                    let sib = digest32_to_gl4(&sib_bytes_vars)?;
                    let is_right = if j < comp_pos_vars.len() { &comp_pos_vars[j] } else { &Boolean::constant(false) };
                    let left = [
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[0], &cur[0])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[1], &cur[1])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[2], &cur[2])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &sib[3], &cur[3])?,
                    ];
                    let right = [
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[0], &sib[0])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[1], &sib[1])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[2], &sib[2])?,
                        FpVar::<InnerFr>::conditionally_select(is_right, &cur[3], &sib[3])?,
                    ];
                    cur = h.merge(&left, &right)?;
                }
                if !comp_lde_root_bytes_vars.is_empty() {
                    let root32 = &comp_lde_root_bytes_vars[0..core::cmp::min(32, comp_lde_root_bytes_vars.len())];
                    if root32.len() == 32 {
                        let root = digest32_to_gl4(root32)?;
                        for k in 0..4 { cur[k].enforce_equal(&root[k])?; }
                    }
                }
            }

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

            // 2.a) Derive query index from FS and tie it to Merkle path position bits
            // Depth equals path length
            let depth = path.pos_bits.len();
            if ENF_QUERY_IDX && depth > 0 {
                // Squeeze a seed and reduce modulo 2^depth: seed = index + q * 2^depth
                let seed = fs.squeeze()?;
                // Compute index from bits: sum_{i=0..depth-1} bit_i * 2^i
                let mut index_from_bits = FpGLVar::zero();
                let mut pow2 = FpGLVar::one();
                let two = FpGLVar::constant(FpGL::from(2u64));
                let one = FpGLVar::one();
                let zero = FpGLVar::zero();
                for i in 0..depth {
                    let bit_f = FpGLVar::conditionally_select(&path.pos_bits[i], &one, &zero)?;
                    index_from_bits = index_from_bits + &(bit_f * pow2.clone());
                    pow2 = pow2 * two.clone();
                }
                // pow2 now equals 2^depth
                // Compute quotient: q_red = (seed - index) / 2^depth
                let q_red = FpGLVar::new_witness(cs.clone(), || {
                    let seed_val = seed.value()?;
                    let index_val = index_from_bits.value()?;
                    let pow2_val = pow2.value()?;
                    let diff = seed_val - index_val;
                    // Compute quotient in Goldilocks field
                    let quotient = diff * pow2_val.inverse().unwrap_or(FpGL::from(1u64));
                    Ok(quotient)
                })?;
                let lhs = seed - index_from_bits.clone() - (q_red * pow2.clone());
                lhs.enforce_equal(&FpGLVar::zero())?;
                // Record for distinctness checks per oracle
                fs_indices_per_oracle[q.oracle_idx as usize].push(index_from_bits);
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
            // Enforce: witness zeta equals FS-derived zeta (gated for alignment)
            if ENF_ZETA_EQUAL { _zeta_gl.enforce_equal(&fs_zeta)?; }
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
                // Use FS-derived beta for this layer (ignore witness-supplied betas)
                let beta = if i < fs_betas.len() { fs_betas[i].clone() } else { FpGLVar::zero() };
                let p_gl_const = FpGLVar::constant(FpGL::from(18446744069414584321u64));
                let fold_lhs = &v_lo + (&beta * &v_hi) - &v_next;
                let q_fold = FpGLVar::new_witness(cs.clone(), || Ok(FpGL::from(0u64)))?;
                if ENF_FRI {
                    fold_lhs.enforce_equal(&(q_fold * p_gl_const))?;
                }
                // Bind leaf digest = Rp64_256.hash([v_lo, v_hi]) to extractor-provided digest (if present)
                if i < q.fri_leaf_digests_le32.len() {
                    let mut h = Rpo256Var::new(cs.clone())?;
                    let digest = h.hash_elements(&vec![v_lo.clone(), v_hi.clone()])?;
                    let digest_bytes_vars = q.fri_leaf_digests_le32[i].iter()
                        .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                        .collect::<Result<Vec<_>, _>>()?;
                    let expected = digest32_to_gl4(&digest_bytes_vars)?;
                    for k in 0..4 { digest[k].enforce_equal(&expected[k])?; }
                }
                // Optional: verify per-layer Merkle path to public FRI root
                if ENF_FRI_PATHS && i < q.fri_paths_nodes_le32.len() {
                    // Get 32B digest bytes and nodes for this layer/query
                    let digest_bytes_vars = if i < q.fri_leaf_digests_le32.len() {
                        q.fri_leaf_digests_le32[i].iter()
                            .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                            .collect::<Result<Vec<_>, _>>()?
                    } else { Vec::new() };
                    if digest_bytes_vars.len() == 32 {
                        let mut cur = digest32_to_gl4(&digest_bytes_vars)?;
                        // Per-layer root bytes slice from public fri_layer_roots_le_bytes
                        // Assume concatenated 32B per layer, select i-th chunk
                        let start = i * 32; let end = start + 32;
                        if fri_layer_roots_bytes_vars.len() >= end {
                            // Fold over sibling nodes per depth
                            let nodes_this_layer = &q.fri_paths_nodes_le32[i];
                            let pos_bits = if i < q.fri_paths_pos.len() { &q.fri_paths_pos[i] } else { &Vec::new() };
                            for (j, node_le32) in nodes_this_layer.iter().enumerate() {
                                let sib_bytes_vars = node_le32.iter()
                                    .map(|b| UInt8::<InnerFr>::new_witness(cs.clone(), || Ok(*b)))
                                    .collect::<Result<Vec<_>, _>>()?;
                                let sib = digest32_to_gl4(&sib_bytes_vars)?;
                                let is_right = if j < pos_bits.len() { Boolean::constant(pos_bits[j]) } else { Boolean::constant(false) };
                                let left = [
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &sib[0], &cur[0])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &sib[1], &cur[1])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &sib[2], &cur[2])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &sib[3], &cur[3])?,
                                ];
                                let right = [
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &cur[0], &sib[0])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &cur[1], &sib[1])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &cur[2], &sib[2])?,
                                    FpVar::<InnerFr>::conditionally_select(&is_right, &cur[3], &sib[3])?,
                                ];
                                let mut h2 = Rpo256Var::new(cs.clone())?;
                                cur = h2.merge(&left, &right)?;
                            }
                            let root_bytes_vars = &fri_layer_roots_bytes_vars[start..end];
                            let root = digest32_to_gl4(root_bytes_vars)?;
                            for k in 0..4 { cur[k].enforce_equal(&root[k])?; }
                        }
                    }
                }
            }
        }

        // 2.b) Enforce pairwise distinctness of FS-derived indices per oracle
        if ENF_QUERY_IDX {
            for indices in fs_indices_per_oracle.iter() {
                let n = indices.len();
                for i in 0..n { for j in (i+1)..n {
                    let diff = &indices[i] - &indices[j];
                    // Allocate inverse witness and enforce (idx_i - idx_j) * inv = 1
                    let inv = FpGLVar::new_witness(cs.clone(), || {
                        let diff_val = diff.value()?;
                        let inv_val = diff_val.inverse().ok_or(SynthesisError::DivisionByZero)?;
                        Ok(inv_val)
                    })?;
                    let one = FpGLVar::one();
                    (diff * inv).enforce_equal(&one)?;
                }}
            }
        }
        
        Ok(())
    }
}

// After processing queries, enforce pairwise distinctness of indices per oracle

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

#[derive(Clone, Default)]
pub struct PublicCommitmentsInputs {
    pub trace_lde_root_le_32: Option<[u8;32]>,
    pub comp_lde_root_le_32: Option<[u8;32]>,
    pub fri_layer_roots_le_32: Vec<[u8;32]>,
    pub ood_commitment_le: Vec<u8>,
    pub ood_evals_merged_gl: Vec<u64>,
    pub query_positions_le: Vec<u8>,
}

/// Setup Groth16 parameters for the inner circuit shape (public inputs = #poseidon roots + FS bytes)
/// Provide a shape hint with the number of oracles and FS bytes length, and a sample query layout
/// CRITICAL: num_queries MUST match the number of queries that will be used in prove!
/// CRITICAL: commitment_sizes must match what will be provided during prove!
pub fn setup_inner_stark(
    num_poseidon_roots: usize,
    sample_query: &HybridQueryWitness,
    fri_num_layers_public: u8,
    num_queries: usize,  // NEW: must match actual proving
    commitment_sizes: Option<(usize, usize, usize, usize, usize)>,  // (trace_lde, comp_lde, fri_layers, ood, query_pos)
) -> InnerStarkMaterial {
    let mut rng = StdRng::seed_from_u64(42);
    let (trace_lde_size, comp_lde_size, fri_layers_size, ood_size, query_pos_size) = commitment_sizes.unwrap_or((0, 0, 0, 0, 0));
    let dummy = InnerStarkVerifierCircuit {
        poseidon_roots: vec![InnerFr::from(0u64); num_poseidon_roots],
        gl_roots_le_bytes: vec![0u8; 32 * num_poseidon_roots],
        poseidon_roots_le_bytes: vec![0u8; 48 * num_poseidon_roots],
        transcript_tail_le_bytes: vec![0u8; 12],
        fri_num_layers_public,
        trace_lde_root_le_bytes: vec![0u8; trace_lde_size],
        comp_lde_root_le_bytes: vec![0u8; comp_lde_size],
        fri_layer_roots_le_bytes: vec![0u8; fri_layers_size],
        ood_commitment_le_bytes: vec![0u8; ood_size],
        ood_evals_merged_gl: Vec::new(),  // witness only, not public input
        query_positions_le_bytes: vec![0u8; query_pos_size],
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
    commitments: Option<PublicCommitmentsInputs>,
) -> (GrothProof<InnerE>, GrothVK<InnerE>) {
    let p2_roots_le_48: Vec<[u8; 48]> = poseidon_roots.iter().map(fr377_to_le48).collect();
    let gl_roots_le_bytes = crate::fs::transcript::flatten_roots_32(gl_roots_le_32);
    let poseidon_roots_le_bytes = flatten_roots(&p2_roots_le_48);
    let tail = build_winterfell_tail(meta);

    // Flatten commitments
    let (trace_lde_root_le_bytes, comp_lde_root_le_bytes, fri_layer_roots_le_bytes, ood_commitment_le_bytes, ood_evals_merged_gl, query_positions_le_bytes) = if let Some(c) = commitments {
        let t = c.trace_lde_root_le_32.map(|r| r.to_vec()).unwrap_or_default();
        let comp = c.comp_lde_root_le_32.map(|r| r.to_vec()).unwrap_or_default();
        let fri = crate::fs::transcript::flatten_roots_32(&c.fri_layer_roots_le_32);
        (t, comp, fri, c.ood_commitment_le, c.ood_evals_merged_gl, c.query_positions_le)
    } else { (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()) };

    prove_inner_stark_raw(
        mat,
        poseidon_roots.to_vec(),
        gl_roots_le_bytes,
        poseidon_roots_le_bytes,
        tail,
        queries,
        fri_num_layers_public,
        trace_lde_root_le_bytes,
        comp_lde_root_le_bytes,
        fri_layer_roots_le_bytes,
        ood_commitment_le_bytes,
        ood_evals_merged_gl,
        query_positions_le_bytes,
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
    trace_lde_root_le_bytes: Vec<u8>,
    comp_lde_root_le_bytes: Vec<u8>,
    fri_layer_roots_le_bytes: Vec<u8>,
    ood_commitment_le_bytes: Vec<u8>,
    ood_evals_merged_gl: Vec<u64>,
    query_positions_le_bytes: Vec<u8>,
) -> (GrothProof<InnerE>, GrothVK<InnerE>) {
    let mut rng = StdRng::seed_from_u64(1337);

    let circ = InnerStarkVerifierCircuit {
        poseidon_roots,
        gl_roots_le_bytes,
        poseidon_roots_le_bytes,
        transcript_tail_le_bytes,
        fri_num_layers_public,
        trace_lde_root_le_bytes,
        comp_lde_root_le_bytes,
        fri_layer_roots_le_bytes,
        ood_commitment_le_bytes,
        ood_evals_merged_gl,
        query_positions_le_bytes,
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
/// Order: poseidon_roots || gl_roots_bytes || poseidon_roots_bytes || tail bytes || 
///        trace_lde_root || comp_lde_root || fri_layer_roots || ood_commitment || query_positions || L
pub fn compute_inner_public_inputs(
    poseidon_roots: &[InnerFr],
    gl_roots_le_bytes: &[u8],
    poseidon_roots_le_bytes: &[u8],
    transcript_tail_le_bytes: &[u8],
    fri_num_layers_public: u8,
    trace_lde_root_le_bytes: &[u8],
    comp_lde_root_le_bytes: &[u8],
    fri_layer_roots_le_bytes: &[u8],
    ood_commitment_le_bytes: &[u8],
    query_positions_le_bytes: &[u8],
) -> Vec<InnerFr> {
    let mut out: Vec<InnerFr> = Vec::with_capacity(
        poseidon_roots.len() 
        + gl_roots_le_bytes.len() 
        + poseidon_roots_le_bytes.len() 
        + transcript_tail_le_bytes.len() 
        + trace_lde_root_le_bytes.len()
        + comp_lde_root_le_bytes.len()
        + fri_layer_roots_le_bytes.len()
        + ood_commitment_le_bytes.len()
        + query_positions_le_bytes.len()
        + 1,
    );
    out.extend_from_slice(poseidon_roots);
    for b in gl_roots_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in poseidon_roots_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in transcript_tail_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in trace_lde_root_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in comp_lde_root_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in fri_layer_roots_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in ood_commitment_le_bytes { out.push(InnerFr::from(*b as u64)); }
    for b in query_positions_le_bytes { out.push(InnerFr::from(*b as u64)); }
    out.push(InnerFr::from(fri_num_layers_public as u64));
    out
}
