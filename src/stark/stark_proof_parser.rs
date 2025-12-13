//! Parse Winterfell STARK Proof into Circuit-Ready Format
//!
//! This module extracts data from a standard Winterfell Proof struct
//! without requiring any hooks or modifications to Winterfell.
//!
//! The Proof struct already contains everything we need:
//! - Commitments (trace, composition, FRI)
//! - Query openings with Merkle batch proofs
//! - OOD frame
//! - FRI layer proofs

use super::gadgets::fri::FriTerminalKind;
use super::inner_stark_full::{
    AirParams, CompQuery, FriLayerQueries, FriQuery, FullStarkVerifierCircuit, TraceQuery,
    TraceSegmentWitness,
};
use crate::stark::StarkInnerFr as InnerFr;
use winter_crypto::{Digest, ElementHasher, RandomCoin};
use winter_math::fields::f64::BaseElement as GL; // Goldilocks field
use winter_math::FieldElement;
use winterfell::Proof;

fn enforce_expected_queries(actual: usize, expected: usize) {
    assert_eq!(
        actual, expected,
        "Proof only contains {actual} unique queries; AIR requires {expected}"
    );
}

pub fn parse_proof_for_circuit_with_query_positions<H, V>(
    proof: &Proof,
    pub_inputs_u64: Vec<u64>,
    air_params: AirParams,
    query_positions: Vec<usize>,
) -> FullStarkVerifierCircuit
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    parse_proof_impl::<H, V>(proof, pub_inputs_u64, air_params, query_positions)
}

/// Derive Winterfell query positions exactly as the verifier does.
pub fn derive_query_positions<H, A>(
    proof: &winterfell::Proof,
    air: &A,
    pub_inputs: &A::PublicInputs,
) -> Vec<usize>
where
    H: winter_crypto::ElementHasher<BaseField = A::BaseField>,
    A: winterfell::Air,
    A::PublicInputs: winter_math::ToElements<A::BaseField>,
{
    use winter_crypto::DefaultRandomCoin;
    use winter_math::ToElements;

    // Seed public coin with verifier context + public inputs.
    let mut public_coin_seed = proof.context.to_elements();
    public_coin_seed.append(&mut pub_inputs.to_elements());
    let mut public_coin = DefaultRandomCoin::<H>::new(&public_coin_seed);

    // Replay verifier transcript to the point where query positions are drawn.
    let num_fri_layers = air
        .options()
        .to_fri_options()
        .num_fri_layers(air.lde_domain_size());
    let (trace_commitments, constraint_commitment, fri_commitments) = proof
        .commitments
        .clone()
        .parse::<H>(air.trace_info().num_segments(), num_fri_layers)
        .expect("parse commitments");

    for trace_root in &trace_commitments {
        public_coin.reseed(*trace_root);
    }
    let _ = air
        .get_constraint_composition_coefficients::<A::BaseField, _>(&mut public_coin)
        .expect("draw constraint coeffs");

    public_coin.reseed(constraint_commitment);
    let _z = public_coin.draw::<A::BaseField>().expect("draw z");

    let (trace_ood_frame, constraint_ood_frame) = proof
        .ood_frame
        .clone()
        .parse::<A::BaseField>(
            air.trace_info().main_trace_width(),
            air.trace_info().aux_segment_width(),
            air.context().num_constraint_composition_columns(),
        )
        .expect("parse OOD");
    use winter_air::proof::merge_ood_evaluations;
    let ood_evals = merge_ood_evaluations(&trace_ood_frame, &constraint_ood_frame);
    public_coin.reseed(H::hash_elements(&ood_evals));

    let _deep_coeffs = air
        .get_deep_composition_coefficients::<A::BaseField, _>(&mut public_coin)
        .expect("draw DEEP coeffs");

    for (i, fri_root) in fri_commitments.iter().enumerate() {
        public_coin.reseed(*fri_root);
        if i < num_fri_layers {
            let _ = public_coin.draw::<A::BaseField>().expect("draw FRI beta");
        }
    }

    let mut query_positions = public_coin
        .draw_integers(
            air.options().num_queries(),
            air.lde_domain_size(),
            proof.pow_nonce,
        )
        .expect("draw query positions");
    query_positions.sort_unstable();
    query_positions.dedup();
    query_positions
}

/// Internal implementation
fn parse_proof_impl<H, V>(
    proof: &Proof,
    pub_inputs_u64: Vec<u64>,
    air_params: AirParams,
    query_positions: Vec<usize>,
) -> FullStarkVerifierCircuit
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    // Use GL (Goldilocks BaseElement) as E
    type E = GL;
    // Extract parameters from proof (don't assume!)
    let num_trace_segments = proof.context.trace_info().num_segments();
    let num_fri_layers = air_params.fri_num_layers;
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    // Use actual number of unique queries from proof (after deduplication)

    // SECURITY (bypass hardening):
    // The Groth16 circuit MUST NOT accept an unconstrained "FS context seed" from the host.
    // We reconstruct the seed inside the circuit from AirParams + public inputs.
    //
    // To ensure our reconstruction matches Winterfell for this proof type, we assert here
    // (host-side) that `proof.context.to_elements()` is exactly the 5-element encoding used
    // by `ParsedProof::context_to_elements()` (trace_width, comp_width, trace_len, lde_blowup, num_queries).
    use winter_math::ToElements;
    let ctx_from_proof: Vec<u64> = proof
        .context
        .to_elements()
        .into_iter()
        .map(|e: GL| e.as_int())
        .collect();
    let num_trace_segments_ctx = proof.context.trace_info().num_segments() as u64;
    let field_modulus_hi32 = 0xFFFF_FFFFu64; // Goldilocks modulus high 32 bits
    let ext_code = 1u64; // FieldExtension::None
    let fri_terminal_degree = match &air_params.fri_terminal {
        super::gadgets::fri::FriTerminalKind::Constant => 0u64,
        super::gadgets::fri::FriTerminalKind::Poly { degree } => *degree as u64,
    };
    let options_pack = (ext_code << 24)
        | ((air_params.fri_folding_factor as u64) << 16)
        | (fri_terminal_degree << 8)
        | (air_params.lde_blowup as u64);
    let ctx_from_params: Vec<u64> = vec![
        // trace_info encoding: (main_width << 8) | aux_width.
        // For our recursive verifier proofs, aux_width is always 0.
        (air_params.trace_width as u64) << 8,
        air_params.trace_len as u64,
        num_trace_segments_ctx,
        field_modulus_hi32,
        air_params.num_constraint_coeffs as u64,
        options_pack,
        air_params.grinding_factor as u64,
        air_params.num_queries as u64,
    ];
    assert_eq!(
        ctx_from_proof,
        ctx_from_params,
        "ProofContext::to_elements() mismatch: proof={ctx_from_proof:?} params={ctx_from_params:?}"
    );

    let (trace_commitments, comp_commitment, fri_commitments) = proof
        .commitments
        .clone()
        .parse::<H>(num_trace_segments, num_fri_layers)
        .map_err(|e| e)
        .expect("parse commitments");

    // Convert to 32-byte arrays
    use winter_crypto::Digest;

    let trace_commitment_le32: Vec<[u8; 32]> =
        trace_commitments.iter().map(|c| c.as_bytes()).collect();
    let comp_commitment_le32: [u8; 32] = comp_commitment.as_bytes();
    let fri_commitments_le32: Vec<[u8; 32]> =
        fri_commitments.iter().map(|c| c.as_bytes()).collect();

    // Use composition width from AirParams (authoritative). Fail fast if missing.
    let comp_width: usize = if air_params.comp_width > 0 {
        air_params.comp_width
    } else {
        panic!("AirParams.comp_width must be set from air.context().num_constraint_composition_columns()");
    };

    // Guard unsupported parameters early for clear errors
    if air_params.fri_folding_factor != 2 {
        panic!(
            "Unsupported FRI folding factor: {} (only binary t=2 is supported currently)",
            air_params.fri_folding_factor
        );
    }
    match air_params.combiner_kind {
        super::gadgets::utils::CombinerKind::RandomRho => {}
        super::gadgets::utils::CombinerKind::DegreeChunks { .. } => {
            panic!("Unsupported combiner: DegreeChunks (only RandomRho is supported currently)");
        }
    }

    // Use provided query positions

    // Parse query openings
    // Ensure the proof opened every configured query position (no silent deduplication).
    let actual_num_queries = proof.num_unique_queries as usize;
    enforce_expected_queries(actual_num_queries, air_params.num_queries);
    assert_eq!(
        query_positions.len(),
        air_params.num_queries,
        "Derived query positions must match AIR num_queries"
    );
    let positions_for_parsing = &query_positions[..];

    // Gather segment widths for all trace commitments (0.13.1 exposes main + aux)
    let trace_info = proof.context.trace_info();
    let main_w = trace_info.main_trace_width();
    let aux_w = trace_info.aux_segment_width();
    let segment_widths: Vec<usize> = (0..num_trace_segments)
        .map(|idx| if idx == 0 { main_w } else { aux_w })
        .collect();

    let trace_segments = parse_trace_queries::<H, V>(
        &proof.trace_queries,
        lde_domain_size,
        actual_num_queries,
        &segment_widths,
        positions_for_parsing,
    );
    let comp_queries = parse_comp_queries::<H, V>(
        &proof.constraint_queries,
        lde_domain_size,
        actual_num_queries,
        comp_width, // Use inferred width!
        positions_for_parsing,
        comp_commitment,
    );
    // Capture composition batch multiproof
    let (comp_batch_proof, comp_table) = proof
        .constraint_queries
        .clone()
        .parse::<E, H, V>(lde_domain_size, actual_num_queries, comp_width)
        .expect("parse comp batch");
    let comp_batch_depth: u8 = comp_batch_proof.depth;
    let tree_num_leaves: usize = 1usize << (comp_batch_depth as usize);
    let mut idxs_aligned: Vec<usize> = positions_for_parsing.iter().map(|&p| p % tree_num_leaves).collect();
    idxs_aligned.truncate(comp_queries.len());

    // Compute leaf digests (for decompression).
    let rows_vec: Vec<Vec<E>> = comp_table.rows().map(|row| row.to_vec()).collect();
    let leaf_digests: Vec<H::Digest> = rows_vec.iter().map(|row| H::hash_elements(row)).collect();

    // Decompress batch proof into fixed-depth per-opening sibling paths.
    let openings = comp_batch_proof
        .into_openings(&leaf_digests, &idxs_aligned)
        .expect("decompress comp batch proof into openings");
    let mut comp_batch_nodes: Vec<Vec<[u8; 32]>> = openings
        .into_iter()
        .map(|(_leaf, siblings)| siblings.into_iter().map(|d| d.as_bytes()).collect())
        .collect();
    let comp_batch_indexes: Vec<usize> = idxs_aligned;
    // Align nodes vector count with number of composition rows
    if comp_batch_nodes.len() < comp_queries.len() {
        let deficit = comp_queries.len() - comp_batch_nodes.len();
        // IMPORTANT (universality): duplicate last real path instead of empty,
        // so downstream batch verification has fixed shape even under collisions.
        if let Some(last) = comp_batch_nodes.last().cloned() {
            comp_batch_nodes.extend(std::iter::repeat(last).take(deficit));
        } else {
            comp_batch_nodes.extend(std::iter::repeat(vec![[0u8; 32]]).take(deficit));
        }
    } else if comp_batch_nodes.len() > comp_queries.len() {
        comp_batch_nodes.truncate(comp_queries.len());
    }

    // Pad/truncate inner node vectors to fixed depth (stabilizes Groth16 constraint shape).
    let comp_target_inner = comp_batch_depth as usize;
    for node_vec in &mut comp_batch_nodes {
        node_vec.truncate(comp_target_inner);
        if node_vec.len() < comp_target_inner {
            node_vec.extend(std::iter::repeat([0u8; 32]).take(comp_target_inner - node_vec.len()));
        }
    }

    // Parse OOD frame
    let main_trace_width = air_params.trace_width;
    let aux_trace_width = proof.context.trace_info().aux_segment_width();
    let num_quotients = comp_width; // Use inferred comp_width!

    let (trace_ood, quotient_ood) = proof
        .ood_frame
        .clone()
        .parse::<E>(main_trace_width, aux_trace_width, num_quotients)
        .expect("parse OOD frame");

    let ood_trace_current: Vec<u64> = trace_ood.current_row().iter().map(|e| e.as_int()).collect();
    let ood_trace_next: Vec<u64> = trace_ood.next_row().iter().map(|e| e.as_int()).collect();

    // OOD composition values (at both z and z*g for LINEAR batching!)
    let ood_comp: Vec<u64> = quotient_ood
        .current_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    let ood_comp_next: Vec<u64> = quotient_ood.next_row().iter().map(|e| e.as_int()).collect();

    // Compute OOD commitment (hash of OOD frame - includes both current and next!)
    let ood_commitment_le32 = compute_ood_commitment::<H>(
        &ood_trace_current,
        &ood_trace_next,
        &ood_comp,
        &ood_comp_next,
    );

    // Parse FRI proof (with positions that fold layer-by-layer)
    // NOTE: Pass full LDE domain size - folding happens INSIDE parse_fri_layers
    let fri_layers = parse_fri_layers::<H, V>(
        &proof.fri_proof,
        num_fri_layers,
        air_params.fri_folding_factor,
        lde_domain_size,  // Full LDE domain, NOT pre-divided
        &query_positions, // Pass main query positions
    );

    // Parse FRI remainder coefficients depending on terminal kind
    let fri_remainder_coeffs: Vec<u64> = match air_params.fri_terminal {
        FriTerminalKind::Poly { .. } => {
            // Parse remainder from FriProof (coefficients in GL), low->high order
            let coeffs_gl: Vec<E> = proof
                .fri_proof
                .clone()
                .parse_remainder::<E>()
                .unwrap_or_else(|_| Vec::new());
            coeffs_gl.iter().map(|e| e.as_int()).collect()
        }
        FriTerminalKind::Constant => Vec::new(),
    };

    // Compute the Groth16 public statement for this circuit.
    //
    // Protocol direction (PVUGC arming):
    // We want the SNARK to be keyed to an arming-friendly statement derived from the
    // VerifierAir public inputs (which include the aggregated statement + interpreter hash),
    // rather than a hash of proof-instance transcript artifacts.
    //
    // IMPORTANT: This is a protocol-level choice. If we do not replay Fiat–Shamir in-circuit,
    // query positions are not derived inside the SNARK; in that case additional binding may be
    // required for full STARK soundness. (See higher-level design notes.)
    let statement_hash = compute_armed_statement_hash_from_verifier_pub_inputs(&pub_inputs_u64);

    FullStarkVerifierCircuit {
        statement_hash,
        stark_pub_inputs: pub_inputs_u64,
        trace_commitment_le32,
        comp_commitment_le32,
        fri_commitments_le32,
        ood_commitment_le32,
        query_positions,
        pow_nonce: proof.pow_nonce,
        trace_segments,
        comp_queries,
        comp_batch_nodes,
        comp_batch_depth,
        comp_batch_indexes,
        ood_trace_current,
        ood_trace_next,
        ood_comp,
        ood_comp_next,
        fri_layers,
        fri_remainder_coeffs,
        air_params,
    }
}

/// Parse trace queries from Winterfell format
fn parse_trace_queries<H, V>(
    queries: &[winter_air::proof::Queries],
    lde_domain_size: usize,
    num_queries: usize,
    segment_widths: &[usize],
    positions: &[usize],
) -> Vec<TraceSegmentWitness>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    if queries.is_empty() {
        return Vec::new();
    }

    let mut segment_witnesses: Vec<TraceSegmentWitness> = Vec::with_capacity(queries.len());

    for (segment_idx, query_set) in queries.iter().enumerate() {
        let width = *segment_widths.get(segment_idx).unwrap_or(&0);
        if width == 0 {
            continue;
        }

        let (batch_proof, table) = query_set
            .clone()
            .parse::<E, H, V>(lde_domain_size, num_queries, width)
            .expect("parse trace queries");

        let rows_vec: Vec<Vec<E>> = table.rows().map(|row| row.to_vec()).collect();
        // Compute leaf digests for Merkle-path decompression.
        let leaf_digests: Vec<H::Digest> = rows_vec.iter().map(|row| H::hash_elements(row)).collect();

        // Sanity: segment row counts consistent across segments
        if !segment_witnesses.is_empty() && segment_witnesses[0].queries.len() != rows_vec.len() {
            panic!(
                "Trace segment row count mismatch: expected {}, got {}",
                segment_witnesses[0].queries.len(),
                rows_vec.len(),
            );
        }

        let mut segment_queries = Vec::with_capacity(rows_vec.len());
        for (_row_idx, row) in rows_vec.iter().enumerate() {
            let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();
            segment_queries.push(TraceQuery {
                values,
                merkle_path: Vec::new(),
                path_positions: Vec::new(),
            });
        }

        let tree_num_leaves: usize = 1usize << (batch_proof.depth as usize);
        let mut idxs_aligned: Vec<usize> = positions.iter().map(|&p| p % tree_num_leaves).collect();
        idxs_aligned.truncate(segment_queries.len());
        // Decompress batch proof into fixed-depth per-opening sibling paths.
        let openings = batch_proof
            .into_openings(&leaf_digests, &idxs_aligned)
            .expect("decompress trace batch proof into openings");
        let mut batch_nodes: Vec<Vec<[u8; 32]>> = openings
            .into_iter()
            .map(|(_leaf, siblings)| siblings.into_iter().map(|d| d.as_bytes()).collect())
            .collect();
        // Align nodes vector count with number of rows for this segment
        if batch_nodes.len() < segment_queries.len() {
            let deficit = segment_queries.len() - batch_nodes.len();
            // IMPORTANT (universality): duplicate last real path instead of empty,
            // so downstream batch verification has fixed shape even under collisions.
            if let Some(last) = batch_nodes.last().cloned() {
                batch_nodes.extend(std::iter::repeat(last).take(deficit));
            } else {
                batch_nodes.extend(std::iter::repeat(vec![[0u8; 32]]).take(deficit));
            }
        } else if batch_nodes.len() > segment_queries.len() {
            batch_nodes.truncate(segment_queries.len());
        }

        // Pad/truncate inner node vectors to fixed depth (stabilizes Groth16 constraint shape).
        let target_inner = tree_num_leaves.trailing_zeros() as usize;
        for node_vec in &mut batch_nodes {
            node_vec.truncate(target_inner);
            if node_vec.len() < target_inner {
                node_vec.extend(std::iter::repeat([0u8; 32]).take(target_inner - node_vec.len()));
            }
        }

        segment_witnesses.push(TraceSegmentWitness {
            queries: segment_queries,
            batch_nodes,
            batch_depth: target_inner as u8,
            batch_indexes: idxs_aligned,
        });
    }

    segment_witnesses
}

/// Parse composition queries
fn parse_comp_queries<H, V>(
    queries: &winter_air::proof::Queries,
    lde_domain_size: usize,
    num_queries: usize,
    values_per_query: usize,
    positions: &[usize],
    _comp_root: H::Digest,
) -> Vec<CompQuery>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    let (batch_proof, table) = queries
        .clone()
        .parse::<E, H, V>(lde_domain_size, num_queries, values_per_query)
        .map_err(|e| e)
        .expect("parse comp queries");

    // Snapshot rows once to avoid iterator-order surprises
    let rows_vec: Vec<Vec<E>> = table.rows().map(|row| row.to_vec()).collect();
    // Compute leaf digests
    let leaves: Vec<H::Digest> = rows_vec.iter().map(|row| H::hash_elements(row)).collect();

    // Use sorted-unique positions modulo tree size, length = leaves.len()
    let tree_num_leaves: usize = 1usize << (batch_proof.depth as usize);
    let mut idxs_aligned: Vec<usize> = positions.iter().map(|&p| p % tree_num_leaves).collect();
    idxs_aligned.truncate(leaves.len());
    // Skip per-path extraction for comp as well; batch verification is enforced in-circuit

    // Align openings by row index
    let aligned_openings: Vec<(Vec<H::Digest>, usize)> = Vec::new();

    rows_vec
        .into_iter()
        .enumerate()
        .map(|(idx, row)| {
            let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();

            // Use aligned openings directly by row index
            let (sib_vec, pos_actual) = aligned_openings
                .get(idx)
                .cloned()
                .unwrap_or((Vec::new(), 0));

            // Bits: current-is-right, LSB-first
            let mut tmp = pos_actual;
            let mut path_positions: Vec<bool> = Vec::with_capacity(sib_vec.len());
            for _ in 0..sib_vec.len() {
                path_positions.push((tmp & 1) == 1);
                tmp >>= 1;
            }

            // Convert siblings to bytes for circuit
            let merkle_path: Vec<[u8; 32]> = Vec::new();

            CompQuery {
                values,
                merkle_path,
                path_positions,
            }
        })
        .collect()
}

/// Parse FRI layers from FRI proof
fn parse_fri_layers<H, V>(
    fri_proof: &winter_fri::FriProof,
    num_layers: usize,
    folding_factor: usize,
    initial_domain_size: usize,
    main_query_positions: &[usize], // Query positions from main DEEP queries
) -> Vec<FriLayerQueries>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;

    // Get num_partitions from proof
    let _num_partitions = fri_proof.num_partitions();

    // Parse all FRI layers
    let (layer_queries, layer_proofs) = fri_proof
        .clone()
        .parse_layers::<E, H, V>(initial_domain_size, folding_factor)
        .expect("parse_layers failed");
    // Structural check: expect exactly num_layers folding layers
    assert!(
        layer_queries.len() == num_layers && layer_proofs.len() == num_layers,
        "FRI layer count mismatch: expected {}, got queries={}, proofs={}",
        num_layers,
        layer_queries.len(),
        layer_proofs.len()
    );

    // Convert to our format
    let mut result = Vec::with_capacity(num_layers);

    let mut layer_positions = main_query_positions.to_vec();
    let mut current_domain_size = initial_domain_size;

    for (_layer_idx, (query_vals, batch_proof)) in
        layer_queries.into_iter().zip(layer_proofs.into_iter()).enumerate()
    {
        // Fold positions for this layer
        // NOTE: Fold using CURRENT domain, then divide (matches Winterfell line 256-257, 303-304)
        let folded_domain_size = current_domain_size / folding_factor;
        assert!(
            current_domain_size % folding_factor == 0,
            "folding factor must divide current domain size"
        );
        layer_positions = layer_positions
            .iter()
            .map(|&p| p % folded_domain_size)
            .collect();
        current_domain_size = folded_domain_size;

        // Deduplicate WITHOUT sorting (preserve insertion order) in O(n)
        // Matches Winterfell's fold_positions but avoids quadratic scanning
        let mut folded_positions = Vec::with_capacity(layer_positions.len());
        {
            use std::collections::HashSet;
            let mut seen: HashSet<usize> =
                HashSet::with_capacity(layer_positions.len().saturating_mul(2));
            for &pos in &layer_positions {
                if seen.insert(pos) {
                    folded_positions.push(pos);
                }
            }
        }

        // query_vals is Vec<E> with folding_factor elements per unique folded position
        assert!(
            query_vals.len() % folding_factor == 0,
            "FRI query_vals length must be divisible by folding_factor"
        );
        let num_uniques = query_vals.len() / folding_factor;
        assert!(
            num_uniques == folded_positions.len(),
            "FRI unique positions count mismatch: folded_positions={}, derived={}",
            folded_positions.len(),
            num_uniques
        );

        // Build per-query FRI data (batch-only; no per-path Merkle data)
        // - query_vals has values for UNIQUE folded positions only
        // - We need to expand back to values for ALL original layer_positions
        // - Multiple original positions may map to the same folded position
        let mut folded_data: std::collections::HashMap<usize, Vec<u64>> =
            std::collections::HashMap::new();

        for (unique_idx, &folded_pos) in folded_positions.iter().enumerate() {
            let chunk_start = unique_idx * folding_factor;
            let chunk_end = (chunk_start + folding_factor).min(query_vals.len());
            let values: Vec<u64> = query_vals[chunk_start..chunk_end]
                .iter()
                .map(|e| e.as_int())
                .collect();
            assert!(
                values.len() == folding_factor,
                "FRI unique folded values must equal folding_factor"
            );
            folded_data.insert(folded_pos, values);
        }

        // Now create one FriQuery per original layer_position
        let mut queries = Vec::with_capacity(layer_positions.len());
        let row_length = current_domain_size;

        for (_pos_idx, &original_pos) in layer_positions.iter().enumerate() {
            let folded_pos = original_pos % row_length;
            let values = folded_data
                .get(&folded_pos)
                .cloned()
                .expect("missing folded data for original position");

            queries.push(FriQuery { values });
        }

        // =========================================================================
        // Universality (Groth16 CRS reuse):
        //
        // We must ensure allocation order inside the Groth16 circuit does NOT depend on
        // proof-dependent index ordering. The simplest way is to carry FRI Merkle openings
        // PER QUERY (length == num_queries) rather than "unique folded positions".
        //
        // We already expanded `queries` to length == num_queries (one per query position),
        // so we also expand Merkle sibling paths to length == num_queries by mapping each
        // query's folded position to its unique opening path.
        // =========================================================================

        // Per-query folded indexes (one per query, may contain duplicates).
        let per_query_indexes: Vec<usize> = layer_positions.clone();
        // Per-query (v_lo, v_hi) pairs in the same order as `layer_positions`.
        let per_query_values: Vec<(u64, u64)> = queries
            .iter()
            .map(|q| {
                assert!(
                    q.values.len() == folding_factor,
                    "FRI per-query values must equal folding_factor"
                );
                (q.values[0], q.values[1])
            })
            .collect();
        // Batch proof structural checks
        let tree_num_leaves: usize = 1usize << (batch_proof.depth as usize);
        assert!(
            tree_num_leaves == current_domain_size,
            "FRI tree leaf count != folded domain size"
        );
        let batch_depth: u8 = batch_proof.depth;

        // Decompress batch proof into per-opening sibling paths for UNIQUE folded positions,
        // then expand to PER-QUERY sibling paths using the per-query folded positions.
        let unique_indexes: Vec<usize> = folded_positions.clone();
        // Compute leaf digests for the UNIQUE openings (each leaf hashes the folding_factor values).
        let leaf_digests: Vec<H::Digest> = unique_indexes
            .iter()
            .map(|idx| {
                let vals = folded_data
                    .get(idx)
                    .cloned()
                    .expect("missing folded data for unique index");
                let elems: Vec<E> = vals
                    .into_iter()
                    .map(|v| E::try_from(v).unwrap_or(E::ZERO))
                    .collect();
                H::hash_elements(&elems)
            })
            .collect();
        let openings = batch_proof
            .into_openings(&leaf_digests, &unique_indexes)
            .expect("decompress FRI batch proof into openings");
        let unique_nodes: Vec<Vec<[u8; 32]>> = openings
            .into_iter()
            .map(|(_leaf, siblings)| siblings.into_iter().map(|d| d.as_bytes()).collect())
            .collect();
        assert!(
            unique_nodes.len() == unique_indexes.len(),
            "FRI openings count mismatch after decompression"
        );
        use std::collections::HashMap;
        let mut nodes_by_index: HashMap<usize, Vec<[u8; 32]>> = HashMap::with_capacity(unique_indexes.len());
        for (idx, nodes) in unique_indexes.iter().copied().zip(unique_nodes.into_iter()) {
            nodes_by_index.insert(idx, nodes);
        }
        let mut batch_nodes: Vec<Vec<[u8; 32]>> = Vec::with_capacity(per_query_indexes.len());
        for idx in &per_query_indexes {
            let nodes = nodes_by_index
                .get(idx)
                .cloned()
                .expect("missing Merkle path for per-query folded index");
            batch_nodes.push(nodes);
        }

        // Pad/truncate inner node vectors to fixed depth (stabilizes Groth16 constraint shape).
        let fri_target_inner = batch_depth as usize;
        for node_vec in &mut batch_nodes {
            node_vec.truncate(fri_target_inner);
            if node_vec.len() < fri_target_inner {
                node_vec.extend(std::iter::repeat([0u8; 32]).take(fri_target_inner - node_vec.len()));
            }
        }

        result.push(FriLayerQueries {
            queries,
            unique_indexes: per_query_indexes,
            unique_values: per_query_values,
            batch_nodes,
            batch_depth,
        });
    }

    result
}

/// Compute OOD commitment (hash of OOD frame)
fn compute_ood_commitment<H: ElementHasher<BaseField = GL>>(
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    ood_comp_next: &[u64],
) -> [u8; 32] {
    use winter_crypto::Digest;

    // Hash OOD frame values - MATCH Winterfell's merge_ood_evaluations order
    // Per Winterfell source: [trace_current, constraint_current, trace_next, constraint_next]
    let mut elements = Vec::new();
    for &v in ood_trace_current {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_comp {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_trace_next {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_comp_next {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }

    let digest = H::hash_elements(&elements);
    digest.as_bytes()
}

/// Poseidon commit to positions (off-chain, matches in-circuit)
fn poseidon_commit_positions_offchain(positions: &[usize]) -> InnerFr {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};

    let mut sponge = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);
    for &pos in positions {
        let b = (pos as u64).to_le_bytes();
        let mut val = 0u64;
        for (i, &byte) in b.iter().enumerate() {
            val |= (byte as u64) << (8 * i);
        }
        sponge.absorb(&InnerFr::from(val));
    }
    sponge.squeeze_field_elements::<InnerFr>(1)[0]
}

/// Compute statement hash binding all public data (including positions and ALL air params)
#[allow(dead_code)]
fn compute_statement_hash(
    trace_roots: &[[u8; 32]],
    comp_root: &[u8; 32],
    fri_roots: &[[u8; 32]],
    ood_commit: &[u8; 32],
    pub_inputs: &[u64],
    query_positions: &[usize],
    air_params: &super::inner_stark_full::AirParams, // Full air_params for complete binding
) -> InnerFr {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;

    let mut hasher = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);

    // Helper: Convert 8 LE bytes to field element
    let bytes_to_fe = |chunk: &[u8]| -> InnerFr {
        let mut val = 0u64;
        for (i, &b) in chunk.iter().enumerate().take(8) {
            val |= (b as u64) << (i * 8);
        }
        InnerFr::from(val)
    };

    // Absorb all commitments
    for trace_root in trace_roots {
        for chunk in trace_root.chunks(8) {
            hasher.absorb(&bytes_to_fe(chunk));
        }
    }
    for chunk in comp_root.chunks(8) {
        hasher.absorb(&bytes_to_fe(chunk));
    }
    for fri_root in fri_roots {
        for chunk in fri_root.chunks(8) {
            hasher.absorb(&bytes_to_fe(chunk));
        }
    }
    for chunk in ood_commit.chunks(8) {
        hasher.absorb(&bytes_to_fe(chunk));
    }

    // Absorb public inputs
    for pub_in in pub_inputs {
        hasher.absorb(&InnerFr::from(*pub_in));
    }

    // Use the *same* positions commitment as the circuit
    let pos_commit = poseidon_commit_positions_offchain(query_positions);
    hasher.absorb(&pos_commit);

    // Compute and absorb air_params hash (MUST match in-circuit computation!)
    // This binds ALL structural params, not just an identity hash.
    let params_hash = compute_air_params_hash(air_params);
    hasher.absorb(&params_hash);

    let hash = hasher.squeeze_field_elements::<InnerFr>(1);
    hash[0]
}

/// Compute the arming-friendly statement hash for Groth16.
///
/// Expected layout is `VerifierPublicInputs::to_elements()`:
/// - Entire public input vector (all words).
fn compute_armed_statement_hash_from_verifier_pub_inputs(pub_inputs: &[u64]) -> InnerFr {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;

    let mut sponge = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);
    // Domain separator for arming statement.
    sponge.absorb(&InnerFr::from(0xA11Du64));
    for &v in pub_inputs {
        sponge.absorb(&InnerFr::from(v));
    }
    sponge.squeeze_field_elements::<InnerFr>(1)[0]
}

/// Compute Poseidon hash of all air_params (must match in-circuit computation exactly!)
fn compute_air_params_hash(air_params: &super::inner_stark_full::AirParams) -> InnerFr {
    use super::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;

    let mut params_hasher = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);

    // Domain separator for AIR params binding (must match circuit!)
    params_hasher.absorb(&InnerFr::from(0xA1A1u64));

    // Absorb all structural params in exact same order as circuit
    params_hasher.absorb(&InnerFr::from(air_params.trace_width as u64));
    params_hasher.absorb(&InnerFr::from(air_params.comp_width as u64));
    params_hasher.absorb(&InnerFr::from(air_params.trace_len as u64));
    params_hasher.absorb(&InnerFr::from(air_params.lde_blowup as u64));
    params_hasher.absorb(&InnerFr::from(air_params.num_queries as u64));
    params_hasher.absorb(&InnerFr::from(air_params.fri_folding_factor as u64));
    params_hasher.absorb(&InnerFr::from(air_params.fri_num_layers as u64));
    params_hasher.absorb(&InnerFr::from(air_params.lde_generator));
    params_hasher.absorb(&InnerFr::from(air_params.domain_offset));
    params_hasher.absorb(&InnerFr::from(air_params.g_lde));
    params_hasher.absorb(&InnerFr::from(air_params.g_trace));
    params_hasher.absorb(&InnerFr::from(air_params.num_constraint_coeffs as u64));
    params_hasher.absorb(&InnerFr::from(air_params.grinding_factor as u64));
    params_hasher.absorb(&InnerFr::from(air_params.combiner_kind.to_u64()));
    params_hasher.absorb(&InnerFr::from(air_params.fri_terminal.to_u64()));
    params_hasher.absorb(&InnerFr::from(air_params.aggregator_version));

    params_hasher.squeeze_field_elements::<InnerFr>(1)[0]
}
