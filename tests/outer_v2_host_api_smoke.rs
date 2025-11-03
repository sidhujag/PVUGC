use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

use arkworks_groth16::outer_compressed as oc;
use arkworks_groth16::*;
use arkworks_groth16::fs::transcript::{fr377_to_le48, flatten_roots, flatten_roots_32, build_winterfell_tail};
use arkworks_groth16::crypto::poseidon_merkle_helpers::merkle_path_default;

#[test]
fn host_api_outer_end_to_end() {
    let mut rng = StdRng::seed_from_u64(123);

    // Minimal inner STARK instance with 2-leaf Merkle path
    let num_oracles = 1usize;
    let a = InnerFr::from(11u64);
    let b = InnerFr::from(22u64);
    let leaves: Vec<InnerFr> = vec![a, b];
    let (root, path, pos) = merkle_path_default(&leaves, 1);

    let q = HybridQueryWitness {
        oracle_idx: 0,
        leaf_bytes: fr377_to_le48(&b).to_vec(),
        poseidon_path_nodes: path,
        poseidon_path_pos: pos,
        gl_leaf_limbs: vec![],
        fri_x_gl: 1,
        fri_zetas_gl: vec![],
        fri_alphas_gl: vec![],
        fri_o_x_gl: vec![],
        fri_o_z_gl: vec![],
        fri_comp_claim_gl: 0,
        fri_layers_v_lo_gl: vec![],
        fri_layers_v_hi_gl: vec![],
        fri_layers_beta_gl: vec![],
        fri_layers_v_next_gl: vec![],
        deep_coeffs_gl: vec![],
        deep_o_x_gl: vec![],
        deep_o_z_gl: vec![],
        deep_z_mult_gl: vec![],
        deep_terms_gl: vec![],
        deep_q_plus_gl: vec![],
        deep_q_minus_gl: vec![],
        deep_den_gl: vec![],
        deep_diff_gl: vec![],
        deep_r_den_gl: vec![],
        deep_r_diff_gl: vec![],
        deep_sum_carry_le_bytes: vec![],
        poseidon_parent1: InnerFr::from(0u64),
        poseidon_l0_sib: InnerFr::from(0u64),
        poseidon_l0_bit: false,
        fri_zeta_gl: 0,
    };

    // Build an inner vk for the shape
    let mat = setup_inner_stark(num_oracles, &q, 0, 1);
    let inner_vk = mat.vk.clone();

    // Inputs
    let poseidon_roots: Vec<InnerFr> = vec![root];
    let gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];
    let meta = WinterfellTailMeta { domain_log2: 0, blowup_log2: 0, num_queries: 0, commitment_roots_le_32: &[], query_positions_le: &[], ood_frame_le: &[], extra: &[] };

    // Compute expected public input count for outer setup
    let p2_roots_le_48: Vec<[u8; 48]> = poseidon_roots.iter().map(fr377_to_le48).collect();
    let gl_roots_bytes = flatten_roots_32(&gl_roots_le_32);
    let p2_roots_bytes = flatten_roots(&p2_roots_le_48);
    let tail = build_winterfell_tail(&meta);
    let n_inputs = poseidon_roots.len() + gl_roots_bytes.len() + p2_roots_bytes.len() + tail.len() + 1;

    // Outer setup using inner vk and correct public input count
    let (pk_outer, _vk_outer) = oc::setup_outer_params(&inner_vk, n_inputs, &mut rng).unwrap();

    // Prove outer with inner STARK via host API
    let (outer_proof, outer_vk, _inner_vk_out, _inner_proof, compressed_public_inputs) = prove_outer_with_inner(
        &pk_outer,
        &inner_vk,
        &poseidon_roots,
        &gl_roots_le_32,
        &meta,
        vec![q],
        0,
        &mut rng,
    );

    // Verify outer via direct API
    assert!(oc::verify_outer(&outer_vk, &compressed_public_inputs, &outer_proof).unwrap());
}


