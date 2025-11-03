use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

use arkworks_groth16::inner_stark::*;
use arkworks_groth16::outer_compressed as oc;
use arkworks_groth16::WinterfellTailMeta;
use winter_crypto::hashers::Blake3_256;
use winterfell::{ProofOptions, FieldExtension, BatchingMethod, Trace};
use winterfell::math::fields::f64::BaseElement;
mod helpers;
use helpers::simple_vdf::{generate_test_vdf_proof, VdfAir, extract_query_leaves};

// Enable arkworks constraint tracing to satisfy runtime checks
fn init_constraint_tracing() {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, Registry};
        // Install only the ConstraintLayer (tracing-subscriber 0.2 API)
        let subscriber = Registry::default()
            .with(ark_relations::r1cs::ConstraintLayer::default());
        let _ = subscriber.try_init();
    });
}

// Full STARK Recursion Test
//
// This test validates end-to-end STARK verification through the hybrid architecture:
//   STARK witnesses → Inner Groth16 (BLS12-377) → Outer Groth16 (BW6-761)
//
// CURRENT STATUS: Validates Poseidon Merkle + FS transcript with minimal data
// TODO: Add real Winterfell STARK witness data (FRI/DEEP/GL)
//
// ROADMAP TO FULL VALIDATION:
// 1. Generate real Winterfell proof (using helpers/simple_vdf.rs)
// 2. Extract witnesses: query leaves, FRI fold data, DEEP evaluations
// 3. Compute shadow Poseidon Merkle paths
// 4. Populate HybridQueryWitness with real FRI/DEEP/GL data
// 5. Validate: Different witnesses (proofs) → Same statement → Proof-agnostic
//
// See: HYBRID_STARK_ARCHITECTURE.md for full security analysis

#[test]
#[ignore]
fn recursion_stark_smoke() {
    init_constraint_tracing();
    // End-to-end recursion with inner STARK constraints using real Winterfell proof extraction

    // 1) Generate a small real Winterfell proof (VDF)
    let start = BaseElement::new(3);
    let steps = 16;
    let (proof, trace) = generate_test_vdf_proof(start, steps);

    // 2) Build matching options and public input
    let options = ProofOptions::new(28, 8, 0, FieldExtension::None, 2, 31, BatchingMethod::Linear, BatchingMethod::Linear);
    let pub_inputs = trace.get(1, trace.length() - 1);

    // 3) Extract GL query leaves first to compute real Poseidon root
    let selected_positions_lde = arkworks_groth16::witness::winterfell_extract::peek_positions_from_proof::<Blake3_256<BaseElement>, VdfAir>(
        &proof, pub_inputs, &options,
    );
    let trace_len = trace.length();
    let mut mapped_rows: Vec<usize> = selected_positions_lde
        .into_iter()
        .map(|p| p % trace_len)
        .collect();
    mapped_rows.sort_unstable();
    mapped_rows.dedup();
    // keep it small for the smoke test
    let mapped_rows: Vec<usize> = mapped_rows.into_iter().take(2).collect();
    let gl_query_leaves = vec![extract_query_leaves(&trace, &mapped_rows)];
    
    // 4) Prepare consistent transcript inputs
    // Use dummy GL roots but let extractor compute real Poseidon roots from leaves
    let gl_roots_le_32: Vec<[u8; 32]> = vec![[0u8; 32]];
    let meta = WinterfellTailMeta { domain_log2: 0, blowup_log2: 0, num_queries: 0, commitment_roots_le_32: &[], query_positions_le: &[], ood_frame_le: &[], extra: &[] };
    let tail_bytes = {
        use arkworks_groth16::fs::transcript::build_winterfell_tail;
        build_winterfell_tail(&meta)
    };

    // 5) Extract real witnesses via verifier replay (pvugc-hooks)
    // Pass empty poseidon_roots - extractor will compute from GL leaves
    let extracted = arkworks_groth16::witness::winterfell_extract::extract_for_inner_from_proof::<Blake3_256<BaseElement>, VdfAir>(
        &proof,
        pub_inputs,
        &options,
        gl_query_leaves,
        gl_roots_le_32.clone(),
        vec![],  // Empty - let extractor compute
        tail_bytes,
    );

    // 6) Prove inner with extracted data (using extracted.poseidon_roots from extractor)
    assert!(!extracted.queries.is_empty(), "should contain at least one query witness");
    let sample_q = extracted.queries[0].clone();
    let num_queries = extracted.queries.len();
    // Compute commitment sizes for setup
    let trace_lde_size = extracted.trace_lde_root_le_32.map(|_| 32).unwrap_or(0);
    let comp_lde_size = extracted.comp_lde_root_le_32.map(|_| 32).unwrap_or(0);
    let fri_layers_size = extracted.fri_layer_roots_le_32.len() * 32;
    let ood_size = extracted.ood_commitment_le.len();
    let query_pos_size = extracted.query_positions.len() * 8;  // 8 bytes per usize
    let commitment_sizes = Some((trace_lde_size, comp_lde_size, fri_layers_size, ood_size, query_pos_size));
    let mat = setup_inner_stark(
        extracted.poseidon_roots.len(), 
        &sample_q, 
        extracted.fri_layers as u8,
        num_queries,
        commitment_sizes,
    );
    let (inner_proof, inner_vk) = prove_inner_stark(
        &mat,
        &extracted.poseidon_roots,
        &extracted.gl_roots_le_32,
        &meta,
        extracted.queries.clone(),
        extracted.fri_layers as u8,
        Some(arkworks_groth16::inner_stark::PublicCommitmentsInputs {
            trace_lde_root_le_32: extracted.trace_lde_root_le_32,
            comp_lde_root_le_32: extracted.comp_lde_root_le_32,
            fri_layer_roots_le_32: extracted.fri_layer_roots_le_32.clone(),
            ood_commitment_le: extracted.ood_commitment_le.clone(),
            ood_evals_merged_gl: extracted.ood_evals_merged_gl.clone(),
            query_positions_le: extracted
                .query_positions
                .iter()
                .flat_map(|p| (p.to_le_bytes()).to_vec())
                .collect(),
        }),
    );

    // 7) Outer compressed proof and verify
    let x_inner = {
        use arkworks_groth16::fs::transcript::{flatten_roots_32, flatten_roots, build_winterfell_tail};
        let p2_le: Vec<[u8; 48]> = extracted.p2_roots_le_48.clone();
        let gl_bytes = flatten_roots_32(&extracted.gl_roots_le_32);
        let p2_bytes = flatten_roots(&p2_le);
        let tail = build_winterfell_tail(&meta);
        // Include commitment bytes in public inputs
        let trace_lde = extracted.trace_lde_root_le_32.map(|r| r.to_vec()).unwrap_or_default();
        let comp_lde = extracted.comp_lde_root_le_32.map(|r| r.to_vec()).unwrap_or_default();
        let fri_roots = flatten_roots_32(&extracted.fri_layer_roots_le_32);
        let query_pos_le: Vec<u8> = extracted.query_positions.iter().flat_map(|p| p.to_le_bytes().to_vec()).collect();
        compute_inner_public_inputs(
            &extracted.poseidon_roots, 
            &gl_bytes, 
            &p2_bytes, 
            &tail, 
            extracted.fri_layers as u8,
            &trace_lde,
            &comp_lde,
            &fri_roots,
            &extracted.ood_commitment_le,
            &query_pos_le,
        )
    };
    let (pk_outer, vk_outer) = oc::setup_outer_params(&inner_vk, x_inner.len(), &mut StdRng::seed_from_u64(123)).expect("outer setup");
    let (proof_outer, _, compressed_public_inputs) = oc::prove_outer(&pk_outer, &inner_vk, &x_inner, &inner_proof, &mut StdRng::seed_from_u64(456)).expect("outer prove");
    let ok = oc::verify_outer(&vk_outer, &compressed_public_inputs, &proof_outer).expect("outer verify");
    assert!(ok, "Recursion STARK smoke test (real) should pass");
}
