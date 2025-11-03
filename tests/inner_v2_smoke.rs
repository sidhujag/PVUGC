// no RNG needed

use arkworks_groth16::inner_stark::*;
use arkworks_groth16::outer_compressed::InnerFr;
use arkworks_groth16::crypto::poseidon_merkle_helpers::{merkle_path_default};
use arkworks_groth16::fs::transcript::fr377_to_le48;
// PoseidonConfig not required for empty-path smoke test

#[test]
fn inner_smoke_minimal() {
    // Two-leaf tree to exercise one-hop path; index=1 (right child)
    let num_oracles = 1usize;
    let a = InnerFr::from(1u64);
    let b = InnerFr::from(2u64);
    let leaves: Vec<InnerFr> = vec![a, b];
    let (root, path, pos) = merkle_path_default(&leaves, 1);
    let pos_for_circuit: Vec<bool> = pos; // helper emits pos=true when current is right

    // One query with leaf/path and no GL constraints
    let q = HybridQueryWitness {
        oracle_idx: 0,
        leaf_bytes: fr377_to_le48(&b).to_vec(),
        poseidon_path_nodes: path,
        poseidon_path_pos: pos_for_circuit,
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

    // Setup with L=0
    let mat = setup_inner_stark(num_oracles, &q, 0, 1, None);

    // Public inputs
    let poseidon_roots: Vec<InnerFr> = vec![root];
    let gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];

    // Minimal Winterfell tail meta
    use arkworks_groth16::WinterfellTailMeta;
    let meta = WinterfellTailMeta {
        domain_log2: 0,
        blowup_log2: 0,
        num_queries: 0,
        commitment_roots_le_32: &[],
        query_positions_le: &[],
        ood_frame_le: &[],
        extra: &[],
    };

    // Prove and verify
    let (proof, vk) = prove_inner_stark(
        &mat,
        &poseidon_roots,
        &gl_roots_le_32,
        &meta,
        vec![q],
        0,
        None,
    );

    let p2_roots_le_48: Vec<[u8; 48]> = vec![fr377_to_le48(&root)];
    let ok_v = verify_inner_stark(
        &vk,
        &proof,
        &poseidon_roots,
        &gl_roots_le_32,
        &p2_roots_le_48,
        &meta,
        0,
    );
    assert!(ok_v, "inner v2 smoke test should pass");
}


