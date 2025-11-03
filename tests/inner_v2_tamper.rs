use arkworks_groth16::inner_stark::*;
use arkworks_groth16::outer_compressed::InnerFr;
use arkworks_groth16::WinterfellTailMeta;
use arkworks_groth16::crypto::poseidon_merkle_helpers::merkle_path_default;
use arkworks_groth16::fs::transcript::fr377_to_le48;
// PoseidonConfig not required for empty-path tamper tests

fn fixture(num_oracles: usize) -> (InnerStarkMaterial, HybridQueryWitness, WinterfellTailMeta<'static>, InnerFr) {
    let leaves: Vec<InnerFr> = vec![InnerFr::from(1u64)];
    let (root, path, pos) = merkle_path_default(&leaves, 0);
    let pos_for_circuit: Vec<bool> = pos;
    let q = HybridQueryWitness {
        oracle_idx: 0,
        leaf_bytes: fr377_to_le48(&leaves[0]).to_vec(),
        poseidon_path_nodes: path,
        poseidon_path_pos: pos_for_circuit,
        // new fields defaulted for this test
        trace_lde_leaf_bytes: Vec::new(),
        trace_lde_path_nodes_le32: Vec::new(),
        trace_lde_path_pos: Vec::new(),
        comp_lde_leaf_bytes: Vec::new(),
        comp_lde_path_nodes_le32: Vec::new(),
        comp_lde_path_pos: Vec::new(),
        fri_leaf_digests_le32: Vec::new(),
        fri_paths_nodes_le32: Vec::new(),
        fri_paths_pos: Vec::new(),
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
    let mat = setup_inner_stark(num_oracles, &q, 0, 1, None);
    let meta = WinterfellTailMeta {
        domain_log2: 0,
        blowup_log2: 0,
        num_queries: 0,
        commitment_roots_le_32: &[],
        query_positions_le: &[],
        ood_frame_le: &[],
        extra: &[],
    };
    (mat, q, meta, root)
}

#[test]
fn tamper_poseidon_root_bytes_fails() {
    let (mat, q, meta, root) = fixture(1);
    let poseidon_roots: Vec<InnerFr> = vec![root];
    let gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];

    let (proof, vk) = prove_inner_stark(&mat, &poseidon_roots, &gl_roots_le_32, &meta, vec![q], 0, None);

    // Build correct p2 roots for verify
    let p2_roots_le_48: Vec<[u8; 48]> = vec![fr377_to_le48(&root)];
    // Tamper one byte in p2 roots
    let mut tampered = p2_roots_le_48.clone();
    tampered[0][0] ^= 1;

    let ok = verify_inner_stark(&vk, &proof, &poseidon_roots, &gl_roots_le_32, &tampered, &meta, 0);
    assert!(!ok, "tampered poseidon root bytes should fail");
}

#[test]
fn tamper_gl_roots_bytes_fails_fs() {
    let (mat, q, meta, root) = fixture(1);
    let poseidon_roots: Vec<InnerFr> = vec![root];
    let mut gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];

    let (proof, vk) = prove_inner_stark(&mat, &poseidon_roots, &gl_roots_le_32, &meta, vec![q], 0, None);

    // Tamper GL root byte; FS should change and verification should fail
    gl_roots_le_32[0][0] ^= 1;
    let p2_roots_le_48: Vec<[u8; 48]> = vec![fr377_to_le48(&root)];
    let ok = verify_inner_stark(&vk, &proof, &poseidon_roots, &gl_roots_le_32, &p2_roots_le_48, &meta, 0);
    assert!(!ok, "tampered GL root bytes should fail FS");
}


