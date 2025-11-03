//! Extract HybridQueryWitness from Winterfell STARK proofs
//!
//! Per expert guidance, this module extracts real STARK witness data using
//! verify_and_log() hooks to populate FRI/DEEP/GL constraints.

use winterfell::Proof;
use winter_math::fields::f64::BaseElement as GL;
use winter_math::FieldElement;
use ark_ff::{PrimeField, Field, BigInteger};

use crate::{
    HybridQueryWitness,
    fs::transcript::fr377_to_le48,
    fs::rpo_gl_host::derive_challenges_from_transcript,
    outer_compressed::InnerFr,
};
use crate::crypto::poseidon_merkle_helpers::merkle_path_default;
use crate::crypto::poseidon_merkle_helpers::verify_path_default;

/// Extracted data ready for inner circuit
#[derive(Clone, Debug)]
pub struct ExtractedForInner {
    pub poseidon_roots: Vec<InnerFr>,      // Fr377 roots (one per oracle)
    pub gl_roots_le_32: Vec<[u8; 32]>,     // GL commitment roots, 32B LE each
    pub p2_roots_le_48: Vec<[u8; 48]>,     // Poseidon roots (for public input binding)
    pub tail_bytes: Vec<u8>,               // canonical Winterfell proof bytes
    pub fri_layers: usize,                 // L
    pub queries: Vec<HybridQueryWitness>,  // per-oracle × per-query
    pub query_positions: Vec<usize>,       // positions used by Winterfell verifier
    // Optional LDE/FRI/OOD exports (to be filled once hooks are wired)
    pub trace_lde_root_le_32: Option<[u8; 32]>,
    pub comp_lde_root_le_32: Option<[u8; 32]>,
    pub fri_layer_roots_le_32: Vec<[u8; 32]>,
    pub ood_commitment_le: Vec<u8>,
    pub ood_evals_merged_gl: Vec<u64>,
}

/// Extract HybridQueryWitness data from Winterfell proof (EXPERT'S EXACT DESIGN)
///
/// This calls verify_and_log() internally to extract real FRI/DEEP witness data.
///
/// # Arguments
/// * `air` - The AIR for verification
/// * `proof` - The Winterfell STARK proof  
/// * `options` - Proof options
/// * `gl_query_leaves` - Query leaf data: [oracle][query_idx][limb_u64]
/// * `gl_commitment_roots_le32` - GL commitment roots (32 bytes LE each)
/// * `poseidon_roots` - Shadow Poseidon Merkle roots (Fr377)
/// * `tail_bytes` - Canonical proof bytes for FS tail
///
/// # Returns
/// ExtractedForInner with real FRI/DEEP/GL witness data
pub fn extract_for_inner_from_proof<H, AIR>(
    proof: &Proof,
    pub_inputs: AIR::PublicInputs,
    options: &winterfell::ProofOptions,
    gl_query_leaves: Vec<Vec<Vec<u64>>>, // [oracle][query_idx][limb_u64]
    gl_commitment_roots_le32: Vec<[u8; 32]>,
    poseidon_roots: Vec<InnerFr>,
    tail_bytes: Vec<u8>,
) -> ExtractedForInner 
where
    H: winter_crypto::ElementHasher<BaseField = GL>,
    AIR: winterfell::Air<BaseField = GL>,
{
    // 1) Run standard Winterfell verify() with logging enabled
    use winter_verifier::{verify, AcceptableOptions, pvugc_hooks::PvugcLog};
    use winter_crypto::RandomCoin;
    
    let mut witness_log = PvugcLog::new();
    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    
    verify::<AIR, H, winter_crypto::DefaultRandomCoin<H>, winter_crypto::MerkleTree<H>>(
        proof.clone(),
        pub_inputs,
        &acceptable,
        Some(&mut witness_log),
    ).expect("winterfell verify with logging");
    
    // 2) Now use the witness_log to build HybridQueryWitness
    // CRITICAL: Use REAL GL roots from witness_log, not dummy passed-in values!
    let real_gl_roots: Vec<[u8; 32]> = if let Some(trace_root) = witness_log.trace_lde_root_le_32 {
        vec![trace_root]  // For now, single oracle (main trace commitment)
    } else {
        gl_commitment_roots_le32.clone()  // Fallback to passed-in (for tests without logging)
    };
    let num_oracles = real_gl_roots.len() as u32;
    let fri_layers = witness_log.fri_layers.len();
    let used_positions = witness_log.query_positions.clone();
    
    // Re-derive circuit challenges (MUST match inner_stark.rs exactly!)
    let (alpha_gl, betas_gl, zeta_host) = derive_challenges_from_transcript(
        num_oracles,
        &real_gl_roots,
        witness_log.trace_lde_root_le_32,
        witness_log.comp_lde_root_le_32,
        &witness_log.fri_layer_roots_le_32,
        &witness_log.ood_commitment_le,
        &tail_bytes,
        fri_layers,
    );
    
    // Build Poseidon Merkle tree from LDE VALUES (from hooks), not trace-domain leaves
    // This ensures consistency: Poseidon shadow tree uses same LDE data as Winterfell's RPO tree
    let lde_leaves_for_poseidon: Vec<Vec<u64>> = if !witness_log.trace_lde_values.is_empty() {
        // Use LDE values BUT respect the test's query limit (gl_query_leaves count)
        let num_leaves_wanted = gl_query_leaves.get(0).map(|v| v.len()).unwrap_or(witness_log.trace_lde_values.len());
        let num_to_use = core::cmp::min(num_leaves_wanted, witness_log.trace_lde_values.len());
        witness_log.trace_lde_values.iter()
            .take(num_to_use)  // Respect test's query limit!
            .map(|row| row.iter().map(|e| e.as_int()).collect())
            .collect()
    } else {
        // Fallback to passed-in gl_query_leaves for tests without hooks
        gl_query_leaves.get(0).cloned().unwrap_or_default()
    };
    
    let (p2_root, p2_paths_nodes, p2_paths_pos, p2_leaves_fr): (InnerFr, Vec<Vec<InnerFr>>, Vec<Vec<bool>>, Vec<InnerFr>) = if !lde_leaves_for_poseidon.is_empty() {
        // Materialize leaf bytes from limbs and convert to Fr377 identically to the circuit
        let mut leaves_fr: Vec<InnerFr> = Vec::with_capacity(lde_leaves_for_poseidon.len());
        for limbs in lde_leaves_for_poseidon.iter() {
            let mut leaf_bytes = Vec::with_capacity(limbs.len() * 8);
            for limb in limbs.iter() { leaf_bytes.extend_from_slice(&limb.to_le_bytes()); }
            leaves_fr.push(InnerFr::from_le_bytes_mod_order(&leaf_bytes));
        }
        // Build root and per-index paths
        let mut paths_nodes: Vec<Vec<InnerFr>> = Vec::with_capacity(leaves_fr.len());
        let mut paths_pos: Vec<Vec<bool>> = Vec::with_capacity(leaves_fr.len());
        let (root, _, _) = merkle_path_default(&leaves_fr, 0);
        for idx in 0..leaves_fr.len() {
            let (_, path_nodes, path_pos) = merkle_path_default(&leaves_fr, idx);
            paths_nodes.push(path_nodes);
            paths_pos.push(path_pos);
        }
        (root, paths_nodes, paths_pos, leaves_fr)
    } else {
        (InnerFr::from(0u64), Vec::new(), Vec::new(), Vec::new())
    };
    
    // Build queries: limited by how many Poseidon paths we actually built
    let available_lde = witness_log.trace_lde_values.len();
    let available_gl = gl_query_leaves.get(0).map(|v| v.len()).unwrap_or(0);
    let num_poseidon_paths = p2_paths_nodes.len();
    
    // CRITICAL: Use whichever is smaller - Poseidon paths built OR Winterfell queries
    let max_q = core::cmp::min(num_poseidon_paths, witness_log.x_points.len());
    let mut queries = Vec::with_capacity(max_q);
    
    eprintln!("DEBUG: Building {} queries (Poseidon paths={}, LDE values={}, GL leaves={})", 
        max_q, num_poseidon_paths, available_lde, available_gl);
    for q_idx in 0..max_q {
        let x = witness_log.x_points[q_idx];
        let comp = witness_log.comp_claims[q_idx];
        // Use Winterfell-logged zeta to match DEEP/comp_claim
        // NOTE: This zeta may differ from circuit-derived zeta if FS transcripts diverge
        // TODO: To enable ENF_ZETA_EQUAL, need to either:
        //   1) Re-compute all DEEP data (ox, oz, comp) using circuit's zeta, OR
        //   2) Ensure Winterfell uses identical FS transcript as circuit
        let zeta = witness_log.zeta.expect("zeta must be logged");
        let den = x - zeta;
        
        // Strict DEEP: take per-term arrays from log
        let strict = &witness_log.deep_strict_per_query[q_idx];
        let deep_coeffs_gl: Vec<u64> = strict.coeffs.iter().map(|v| v.as_int()).collect();
        let deep_o_x_gl: Vec<u64> = strict.ox.iter().map(|v| v.as_int()).collect();
        let deep_o_z_gl: Vec<u64> = strict.oz.iter().map(|v| v.as_int()).collect();
        let deep_z_mult_gl: Vec<u64> = strict.z_mults.iter().map(|v| v.as_int()).collect();
        // Precompute per-term values term_i = coeff_i*(ox_i - oz_i)/(x - zeta*mult_i) in GL
        // and the integer quotient q_i such that t_i*den_i = num_i + q_i*p_GL
        let mut deep_terms_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_q_plus_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_q_minus_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_den_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_diff_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_r_den_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let mut deep_r_diff_gl: Vec<u64> = Vec::with_capacity(deep_coeffs_gl.len());
        let p_gl_u128: u128 = 18446744069414584321u128;
        for i in 0..deep_coeffs_gl.len() {
            let coeff = strict.coeffs[i];
            let ox = strict.ox[i];
            let oz = strict.oz[i];
            let mult = strict.z_mults[i];
            
            // Compute diff and den using GL field (canonical by construction)
            let ox_minus_oz = ox - oz;
            let diff_u64 = ox_minus_oz.as_int();  // Already canonical in GL
            let den_gl = x - (zeta * mult);
            let den_u64 = den_gl.as_int();  // Already canonical in GL
            
            deep_den_gl.push(den_u64);
            deep_diff_gl.push(diff_u64);
            
            // Compute r_den and r_diff for Fr377 modular reduction
            // Circuit computes: x_fr377 - (zeta_fr377 * mult_fr377) in Fr377 field
            // This can wrap around differently than GL field!
            let x_fr = InnerFr::from(x.as_int());
            let zeta_fr = InnerFr::from(zeta.as_int());
            let mult_fr = InnerFr::from(mult.as_int());
            let den_raw_fr = x_fr - (zeta_fr * mult_fr);  // In Fr377
            let den_canonical_fr = InnerFr::from(den_u64);  // GL canonical value in Fr377
            let p_gl_fr = InnerFr::from(p_gl_u128 as u64);
            
            // NOTE: r_den and r_diff not used (would require > u64 values)
            deep_r_den_gl.push(0u64);
            deep_r_diff_gl.push(0u64);
            
            // Compute term in GL field (to match Winterfell's DEEP computation)
            let term_gl = (coeff * ox_minus_oz) * den_gl.inv();
            let term_u64 = term_gl.as_int();
            deep_terms_gl.push(term_u64);
            
            // Compute q for Fr377 constraint: term * den - coeff * diff = q * p_gl
            let term_fr = InnerFr::from(term_u64);
            let den_fr = InnerFr::from(den_u64);
            let coeff_fr = InnerFr::from(coeff.as_int());
            let diff_fr = InnerFr::from(diff_u64);
            let p_gl_fr = InnerFr::from(p_gl_u128 as u64);
            
            // lhs = term * den - coeff * diff in Fr377
            let lhs_fr = term_fr * den_fr - coeff_fr * diff_fr;
            
            // q = lhs / p_gl in Fr377
            let q_fr = lhs_fr * p_gl_fr.inverse().unwrap();
            
            // Extract q as u64
            let q_bigint = q_fr.into_bigint();
            let q_bytes = q_bigint.to_bytes_le();
            let q_u64 = u64::from_le_bytes([q_bytes[0], q_bytes[1], q_bytes[2], q_bytes[3],
                                           q_bytes[4], q_bytes[5], q_bytes[6], q_bytes[7]]);
            
            // Handle sign
            if q_u64 == 0 {
                deep_q_plus_gl.push(0u64);
                deep_q_minus_gl.push(0u64);
            } else if q_fr.into_bigint() > InnerFr::MODULUS_MINUS_ONE_DIV_TWO.into() {
                // Negative
                let q_neg = -q_fr;
                let q_neg_bytes = q_neg.into_bigint().to_bytes_le();
                let q_neg_u64 = u64::from_le_bytes([q_neg_bytes[0], q_neg_bytes[1], q_neg_bytes[2], q_neg_bytes[3],
                                                    q_neg_bytes[4], q_neg_bytes[5], q_neg_bytes[6], q_neg_bytes[7]]);
                deep_q_plus_gl.push(0u64);
                deep_q_minus_gl.push(q_neg_u64);
            } else {
                deep_q_plus_gl.push(q_u64);
                deep_q_minus_gl.push(0u64);
            }
        }
        
        // Compute carry for sum constraint: sum - comp_claim = carry * p_gl (in Fr377)
        let mut sum_fr = InnerFr::from(0u64);
        for term_u64 in &deep_terms_gl {
            sum_fr += InnerFr::from(*term_u64);
        }
        let comp_fr = InnerFr::from(comp.as_int());
        let p_gl_fr = InnerFr::from(p_gl_u128 as u64);
        let carry_fr = (sum_fr - comp_fr) * p_gl_fr.inverse().unwrap();
        let carry_bytes = carry_fr.into_bigint().to_bytes_le();
        
        // Sanity: sum of terms equals comp mod p_gl
        let sum_terms_mod: u128 = deep_terms_gl.iter().fold(0u128, |acc, t| (acc + *t as u128) % p_gl_u128);
        if sum_terms_mod as u64 != comp.as_int() {
            eprintln!("ERROR q_idx={}: sum_terms={}, comp={}", q_idx, sum_terms_mod, comp.as_int());
        }
        assert_eq!(sum_terms_mod as u64, comp.as_int(), "sum terms != comp_claim (mod p_gl) at query {q_idx}");
        
        // FRI fold data per layer
        let mut fri_v_lo = Vec::with_capacity(fri_layers);
        let mut fri_v_hi = Vec::with_capacity(fri_layers);
        let mut fri_v_next = Vec::with_capacity(fri_layers);
        
        for layer in 0..fri_layers {
            let fold = &witness_log.fri_layers[layer][q_idx];
            fri_v_lo.push(fold.v_lo.as_int());
            fri_v_hi.push(fold.v_hi.as_int());
            fri_v_next.push(fold.v_next.as_int());
            // Debug: check fold relation with derived beta
            let beta = betas_gl[layer];
            let lhs = (fold.v_lo + beta * fold.v_hi).as_int();
            let rhs = fold.v_next.as_int();
            assert_eq!(lhs, rhs, "FRI fold mismatch at q={q_idx}, layer={layer}");
        }
        
        // Get GL leaf limbs for this query - use LDE VALUES from hooks!
        let gl_limbs = if !witness_log.trace_lde_values.is_empty() && q_idx < witness_log.trace_lde_values.len() {
            // Use actual LDE values from Winterfell (correct domain!)
            witness_log.trace_lde_values[q_idx].iter().map(|e| e.as_int()).collect()
        } else {
            // Fallback to passed-in trace-domain values (for legacy tests)
            gl_query_leaves
                .get(0)
            .and_then(|qs| qs.get(q_idx))
            .cloned()
                .unwrap_or_default()
        };
        
        // Build leaf_bytes from GL limbs (LE 8-byte encoding)
        let mut leaf_bytes = Vec::with_capacity(gl_limbs.len() * 8);
        for limb in &gl_limbs { leaf_bytes.extend_from_slice(&limb.to_le_bytes()); }
        
        // Convert to Fr377 for Poseidon Merkle using the same LE-bytes
        let leaf_fr = InnerFr::from_le_bytes_mod_order(&leaf_bytes);
        
        // DEBUG: Verify this leaf matches what was used to build the Poseidon tree
        if !lde_leaves_for_poseidon.is_empty() && q_idx < lde_leaves_for_poseidon.len() {
            let tree_leaf_limbs = &lde_leaves_for_poseidon[q_idx];
            if &gl_limbs != tree_leaf_limbs {
                eprintln!("ERROR q_idx={}: gl_limbs != tree_leaf!", q_idx);
                eprintln!("  gl_limbs={:?}", &gl_limbs[..core::cmp::min(4, gl_limbs.len())]);
                eprintln!("  tree_leaf={:?}", &tree_leaf_limbs[..core::cmp::min(4, tree_leaf_limbs.len())]);
            }
        }
        // Real Poseidon path per query (if available)
        let (poseidon_path_nodes, poseidon_path_pos) = if !p2_paths_nodes.is_empty() && q_idx < p2_paths_nodes.len() {
            (p2_paths_nodes[q_idx].clone(), p2_paths_pos[q_idx].clone())
        } else { (Vec::new(), Vec::new()) };
        if !poseidon_path_nodes.is_empty() {
            eprintln!("DEBUG: HOST verifying Poseidon path for q_idx={}", q_idx);
            let ok = verify_path_default(leaf_fr, &poseidon_path_nodes, &poseidon_path_pos, p2_root);
            assert!(ok, "poseidon merkle path failed at query {q_idx}");
            eprintln!("DEBUG: HOST Poseidon path OK for q_idx={}", q_idx);
        }

        // Use path_pos directly - circuit uses same convention as host
        let path_pos_for_circuit: Vec<bool> = poseidon_path_pos.clone();

        // Compute first-level parent for debugging: parent1 = H(sib, leaf) if pos[0]=true else H(leaf, sib)
        let poseidon_parent1: InnerFr = if !poseidon_path_nodes.is_empty() {
            let sib0 = poseidon_path_nodes[0];
            if path_pos_for_circuit[0] { // current is RIGHT; parent(left=sib, right=leaf)
                crate::crypto::poseidon_merkle_helpers::poseidon2_merkle_parent(&crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1, sib0, leaf_fr)
            } else { // current is LEFT; parent(left=leaf, right=sib)
                crate::crypto::poseidon_merkle_helpers::poseidon2_merkle_parent(&crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1, leaf_fr, sib0)
            }
        } else { leaf_fr };

        // Debug l0 values before moving nodes/pos into witness
        let (poseidon_l0_sib, poseidon_l0_bit) = if !poseidon_path_nodes.is_empty() {
            (poseidon_path_nodes[0], poseidon_path_pos[0])
        } else { (leaf_fr, false) };
        
        // Fill LDE placeholders from witness_log if present
        let trace_lde_path_nodes_le32 = witness_log.trace_paths_nodes_le_32.get(q_idx).cloned().unwrap_or_default();
        let trace_lde_path_pos = witness_log.trace_paths_pos.get(q_idx).cloned().unwrap_or_default();
        let comp_lde_path_nodes_le32 = witness_log.comp_paths_nodes_le_32.get(q_idx).cloned().unwrap_or_default();
        let comp_lde_path_pos = witness_log.comp_paths_pos.get(q_idx).cloned().unwrap_or_default();

        // Prefer logged leaf digests (32B) if present
        let trace_lde_leaf_bytes = witness_log
            .trace_leaf_digests_le_32
            .get(q_idx)
            .map(|a| a.to_vec())
            .unwrap_or_else(|| Vec::new());
        let comp_lde_leaf_bytes = witness_log
            .comp_leaf_digests_le_32
            .get(q_idx)
            .map(|a| a.to_vec())
            .unwrap_or_else(|| Vec::new());

        queries.push(HybridQueryWitness {
            oracle_idx: 0,
            leaf_bytes,
            poseidon_path_nodes: poseidon_path_nodes.clone(),
            poseidon_path_pos: path_pos_for_circuit.clone(),
            trace_lde_leaf_bytes,
            trace_lde_path_nodes_le32,
            trace_lde_path_pos,
            comp_lde_leaf_bytes,
            comp_lde_path_nodes_le32,
            comp_lde_path_pos,
            fri_leaf_digests_le32: if !witness_log.fri_layer_leaf_digests_le_32.is_empty() {
                let mut out: Vec<[u8;32]> = Vec::with_capacity(witness_log.fri_layer_leaf_digests_le_32.len());
                for layer in 0..witness_log.fri_layer_leaf_digests_le_32.len() {
                    let vec_for_layer = &witness_log.fri_layer_leaf_digests_le_32[layer];
                    if q_idx < vec_for_layer.len() { out.push(vec_for_layer[q_idx]); }
                }
                out
            } else { Vec::new() },
            fri_paths_nodes_le32: Vec::new(),
            fri_paths_pos: Vec::new(),
            gl_leaf_limbs: gl_limbs,
            
            fri_x_gl: x.as_int(),
            fri_zeta_gl: zeta.as_int(),
            fri_zetas_gl: vec![],
            fri_alphas_gl: vec![],
            fri_o_x_gl: vec![],
            fri_o_z_gl: vec![],
            fri_comp_claim_gl: comp.as_int(),

            deep_coeffs_gl,
            deep_o_x_gl,
            deep_o_z_gl,
            deep_z_mult_gl,
            deep_terms_gl,
            deep_q_plus_gl,
            deep_q_minus_gl,
            deep_den_gl,
            deep_diff_gl,
            deep_r_den_gl,
            deep_r_diff_gl,
            
            fri_layers_v_lo_gl: fri_v_lo,
            fri_layers_v_hi_gl: fri_v_hi,
            fri_layers_beta_gl: betas_gl.iter().map(|b| b.as_int()).collect(),
            fri_layers_v_next_gl: fri_v_next,
            
            deep_sum_carry_le_bytes: carry_bytes.to_vec(),

            poseidon_parent1,
            poseidon_l0_sib,
            poseidon_l0_bit: if !path_pos_for_circuit.is_empty() { path_pos_for_circuit[0] } else { false },
        });
    }
    
    // Poseidon root(s): prefer computed root if GL leaves were provided
    let final_poseidon_roots: Vec<InnerFr> = if !p2_paths_nodes.is_empty() { vec![p2_root] } else { poseidon_roots };
    let p2_roots_le_48 = final_poseidon_roots.iter().map(|r| fr377_to_le48(r)).collect();
    
    ExtractedForInner {
        queries,
        gl_roots_le_32: real_gl_roots,  // Use REAL roots for FS derivation
        poseidon_roots: final_poseidon_roots,
        p2_roots_le_48,
        tail_bytes,
        fri_layers,
        query_positions: used_positions,
        trace_lde_root_le_32: witness_log.trace_lde_root_le_32,
        comp_lde_root_le_32: witness_log.comp_lde_root_le_32,
        fri_layer_roots_le_32: witness_log.fri_layer_roots_le_32.clone(),
        ood_commitment_le: witness_log.ood_commitment_le.clone(),
        ood_evals_merged_gl: witness_log.ood_evals_merged.iter().map(|e| e.as_int()).collect(),
    }
}

/// Peek query positions from a Winterfell proof (for building GL leaves in correct order)
pub fn peek_positions_from_proof<H, AIR>(
    proof: &Proof,
    pub_inputs: AIR::PublicInputs,
    options: &winterfell::ProofOptions,
) -> Vec<usize>
where
    H: winter_crypto::ElementHasher<BaseField = GL>,
    AIR: winterfell::Air<BaseField = GL>,
{
    use winter_verifier::{verify, AcceptableOptions, pvugc_hooks::PvugcLog};
    let mut witness_log = PvugcLog::new();
    let acceptable = AcceptableOptions::OptionSet(vec![options.clone()]);
    verify::<AIR, H, winter_crypto::DefaultRandomCoin<H>, winter_crypto::MerkleTree<H>>(
        proof.clone(),
        pub_inputs,
        &acceptable,
        Some(&mut witness_log),
    ).expect("winterfell verify with logging");
    witness_log.query_positions
}

//  ============================================================================
//  BLOCKING ON EXPERT IMPLEMENTATION
//  ============================================================================
//
//  The function above (extract_for_inner_with_log) is COMPLETE per expert code.
//
//  WHAT'S BLOCKING:
//    winterfell-pvugc/verifier/src/pvugc_hooks.rs::verify_and_log()
//
//  This requires exact Winterfell 0.13.1 internal verifier API knowledge:
//    - How to hook VerifierChannel methods
//    - How to access FriVerifier internals  
//    - How to capture x_points, comp_claims, zeta, fri_layers
//
//  READY FOR EXPERT:
//    - All our code is in place (FS fixed, RPO host ready, extractor ready)
//    - Need exact verify_and_log() implementation for Winterfell 0.13.1
//    - See: EXPERT_QUESTION.md
//
//  ============================================================================
