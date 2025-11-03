use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

use arkworks_groth16::outer_compressed as oc;
use arkworks_groth16::*;
use arkworks_groth16::fs::transcript::{flatten_roots_32, fr377_to_le48, flatten_roots, build_winterfell_tail};
use arkworks_groth16::crypto::poseidon_merkle_helpers::merkle_path_default;

#[test]
fn outer_recursion_verifies_inner_v2() {
    let mut rng = StdRng::seed_from_u64(42);

    // Inner STARK with real Poseidon Merkle path (2-leaf tree to exercise sibling logic)
    let num_oracles = 1usize;
    let a = InnerFr::from(7u64);
    let b = InnerFr::from(13u64);
    let leaves: Vec<InnerFr> = vec![a, b];
    let (root, path, pos) = merkle_path_default(&leaves, 1);  // Index=1 (right child)
    let pos_for_circuit: Vec<bool> = pos;
    let q = HybridQueryWitness {
        oracle_idx: 0,
        leaf_bytes: fr377_to_le48(&b).to_vec(),
        poseidon_path_nodes: path,
        poseidon_path_pos: pos_for_circuit,
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
    let mat = setup_inner_stark(num_oracles, &q, 0, 1);
    let poseidon_roots: Vec<InnerFr> = vec![root];
    let gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];
    let meta = WinterfellTailMeta { domain_log2: 0, blowup_log2: 0, num_queries: 0, commitment_roots_le_32: &[], query_positions_le: &[], ood_frame_le: &[], extra: &[] };
    let (inner_proof, inner_vk) = prove_inner_stark(&mat, &poseidon_roots, &gl_roots_le_32, &meta, vec![q], 0);

    // Build inner public inputs for outer circuit
    let p2_roots_le_48: Vec<[u8; 48]> = poseidon_roots.iter().map(fr377_to_le48).collect();
    let gl_roots_bytes = flatten_roots_32(&gl_roots_le_32);
    let p2_roots_bytes = flatten_roots(&p2_roots_le_48);
    let tail = build_winterfell_tail(&meta);
    let x_inner = compute_inner_public_inputs(&poseidon_roots, &gl_roots_bytes, &p2_roots_bytes, &tail, 0);

    // Outer setup and verify inner proof in-circuit
    let (pk_outer, vk_outer) = oc::setup_outer_params(&inner_vk, x_inner.len(), &mut rng).unwrap();
    let (proof_outer, _vk_from_prove, compressed_public_inputs) = oc::prove_outer(&pk_outer, &inner_vk, &x_inner, &inner_proof, &mut rng).unwrap();
    
    // Verify using the compressed public inputs returned by prove_outer
    // (BooleanInputVar compresses 94 inner elements to 64 outer elements)
    assert!(oc::verify_outer(&vk_outer, &compressed_public_inputs, &proof_outer).unwrap(), 
        "Outer proof verification failed");
}


