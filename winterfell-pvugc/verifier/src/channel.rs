// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use alloc::{string::ToString, vec::Vec};
use core::marker::PhantomData;

use air::{
    proof::{Proof, Queries, QuotientOodFrame, Table, TraceOodFrame},
    Air,
};
use crypto::{ElementHasher, VectorCommitment};
use fri::VerifierChannel as FriVerifierChannel;
use math::{FieldElement, StarkField};

use crate::VerifierError;

#[cfg(feature = "pvugc-hooks")]
fn compute_openings_from_batch<E, H>(
    proof: &crate::crypto::BatchMerkleProof<H>,
    leaves: &[H::Digest],
    indexes: &[usize],
) -> Result<Vec<(H::Digest, Vec<H::Digest>)>, VerifierError>
where
    E: FieldElement,
    H: crypto::Hasher,
{
    use alloc::collections::BTreeMap;
    // Build partial tree map as in into_openings without consuming proof
    let mut partial_tree_map = BTreeMap::new();
    let depth = proof.depth as usize;
    // Seed leaves
    for (&i, leaf) in indexes.iter().zip(leaves.iter()) {
        partial_tree_map.insert(i + (1 << depth), *leaf);
    }

    // Replace odd indexes, offset, and sort
    // Reuse normalize_indexes/map_indexes from merkle::mod via functions not exposed; instead, mimic
    // Build map from original index to compacted position
    let num_leaves = 1usize << depth;
    let mut map = BTreeMap::new();
    for (pos, &idx) in indexes.iter().enumerate() {
        if idx >= num_leaves { return Err(VerifierError::ProofDeserializationError("index OOB".into())); }
        if map.insert(idx, pos).is_some() { return Err(VerifierError::ProofDeserializationError("dup index".into())); }
    }
    // Normalize indexes (set even indices for sibling pairs)
    let mut norm: alloc::vec::Vec<usize> = alloc::vec::Vec::new();
    for &idx in indexes {
        let even = idx - (idx & 1);
        if norm.last().copied() != Some(even) { norm.push(even); }
    }
    if norm.len() != proof.nodes.len() {
        return Err(VerifierError::ProofDeserializationError("invalid batch proof".into()));
    }

    // For each normalized index, compute parents and fill partial tree map similarly to get_root
    let offset = 1usize << depth;
    let mut next_indexes: alloc::vec::Vec<usize> = alloc::vec::Vec::new();
    let mut proof_pointers: alloc::vec::Vec<usize> = alloc::vec::Vec::with_capacity(norm.len());
    let mut buf = [H::Digest::default(); 2];
    for (i, index) in norm.iter().copied().enumerate() {
        match map.get(&index) {
            Some(&i1) => {
                if leaves.len() <= i1 { return Err(VerifierError::ProofDeserializationError("invalid leaves".into())); }
                buf[0] = leaves[i1];
                match map.get(&(index + 1)) {
                    Some(&i2) => {
                        if leaves.len() <= i2 { return Err(VerifierError::ProofDeserializationError("invalid leaves".into())); }
                        buf[1] = leaves[i2];
                        proof_pointers.push(0);
                    }
                    None => {
                        if proof.nodes[i].is_empty() { return Err(VerifierError::ProofDeserializationError("invalid proof".into())); }
                        buf[1] = proof.nodes[i][0];
                        proof_pointers.push(1);
                    }
                }
            }
            None => {
                if proof.nodes[i].is_empty() { return Err(VerifierError::ProofDeserializationError("invalid proof".into())); }
                buf[0] = proof.nodes[i][0];
                match map.get(&(index + 1)) {
                    Some(&i2) => {
                        if leaves.len() <= i2 { return Err(VerifierError::ProofDeserializationError("invalid leaves".into())); }
                        buf[1] = leaves[i2];
                    }
                    None => return Err(VerifierError::ProofDeserializationError("invalid proof".into())),
                }
                proof_pointers.push(1);
            }
        }
        let parent = H::merge(&buf);
        partial_tree_map.insert(offset + index, buf[0]);
        partial_tree_map.insert((offset + index) ^ 1, buf[1]);
        let parent_index = (offset + index) >> 1;
        partial_tree_map.insert(parent_index, parent);
        next_indexes.push(parent_index);
    }
    // Iterate up
    for _ in 1..depth {
        let cur = next_indexes.clone();
        next_indexes.clear();
        let mut i = 0;
        while i < cur.len() {
            let node_index = cur[i];
            let sibling_index = node_index ^ 1;
            let sibling = if i + 1 < cur.len() && cur[i + 1] == sibling_index {
                i += 1;
                match partial_tree_map.get(&sibling_index) {
                    Some(s) => *s,
                    None => return Err(VerifierError::ProofDeserializationError("missing sibling".into())),
                }
            } else {
                let pointer = proof_pointers[i];
                if proof.nodes[i].len() <= pointer { return Err(VerifierError::ProofDeserializationError("invalid pointer".into())); }
                // record sibling
                proof_pointers[i] += 1;
                proof.nodes[i][pointer]
            };
            partial_tree_map.insert(node_index ^ 1, sibling);
            let node = match partial_tree_map.get(&node_index) { Some(n) => *n, None => return Err(VerifierError::ProofDeserializationError("missing node".into())), };
            let parent = if node_index & 1 != 0 { H::merge(&[sibling, node]) } else { H::merge(&[node, sibling]) };
            let parent_index = node_index >> 1;
            partial_tree_map.insert(parent_index, parent);
            next_indexes.push(parent_index);
            i += 1;
        }
    }
    // Build per-index proofs directly from partial tree
    let mut outs = alloc::vec::Vec::with_capacity(indexes.len());
    for &idx in indexes {
        let mut cur = idx + (1 << depth);
        let leaf = match partial_tree_map.get(&cur) { Some(v) => *v, None => return Err(VerifierError::ProofDeserializationError("leaf missing".into())) };
        let mut proof_vec: alloc::vec::Vec<H::Digest> = alloc::vec::Vec::new();
        while cur > 1 {
            let sib_idx = cur ^ 1;
            let sib = match partial_tree_map.get(&sib_idx) { Some(v) => *v, None => return Err(VerifierError::ProofDeserializationError("sib missing".into())) };
            proof_vec.push(sib);
            cur >>= 1;
        }
        outs.push((leaf, proof_vec));
    }
    Ok(outs)
}

// VERIFIER CHANNEL
// ================================================================================================

/// A view into a [Proof] for a computation structured to simulate an "interactive" channel.
///
/// A channel is instantiated for a specific proof, which is parsed into structs over the
/// appropriate field (specified by type parameter `E`). This also validates that the proof is
/// well-formed in the context of the computation for the specified [Air].
pub struct VerifierChannel<
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
> {
    // trace queries
    trace_commitments: Vec<H::Digest>,
    trace_queries: Option<TraceQueries<E, H, V>>,
    // constraint queries
    constraint_commitment: H::Digest,
    constraint_queries: Option<ConstraintQueries<E, H, V>>,
    // partition sizes for the rows of main, auxiliary and constraint traces rows
    partition_size_main: usize,
    partition_size_aux: usize,
    partition_size_constraint: usize,
    // FRI proof
    fri_commitments: Option<Vec<H::Digest>>,
    fri_layer_proofs: Vec<V::MultiProof>,
    fri_layer_queries: Vec<Vec<E>>,
    fri_remainder: Option<Vec<E>>,
    fri_num_partitions: usize,
    // out-of-domain frame
    ood_trace_frame: Option<TraceOodFrame<E>>,
    ood_constraint_evaluations: Option<QuotientOodFrame<E>>,
    // query proof-of-work
    pow_nonce: u64,
    // PVUGC logging fields (feature-gated)
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_trace_paths_nodes: Option<Vec<Vec<H::Digest>>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_trace_paths_pos: Option<Vec<Vec<bool>>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_comp_paths_nodes: Option<Vec<Vec<H::Digest>>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_comp_paths_pos: Option<Vec<Vec<bool>>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_fri_layer_roots: Vec<H::Digest>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_trace_leaf_digests: Option<Vec<H::Digest>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_comp_leaf_digests: Option<Vec<H::Digest>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_fri_layer_positions: Vec<Vec<usize>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_fri_layer_leaf_digests: Vec<Vec<H::Digest>>,
    #[cfg(feature = "pvugc-hooks")]
    pub pvugc_fri_layer_paths_nodes: Vec<Vec<H::Digest>>,
}

impl<E, H, V> VerifierChannel<E, H, V>
where
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H, MultiProof = crate::crypto::BatchMerkleProof<H>>,
{
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    /// Creates and returns a new [VerifierChannel] initialized from the specified `proof`.
    pub fn new<A: Air<BaseField = E::BaseField>>(
        air: &A,
        proof: Proof,
    ) -> Result<Self, VerifierError> {
        let Proof {
            context,
            num_unique_queries,
            commitments,
            trace_queries,
            constraint_queries,
            ood_frame,
            fri_proof,
            pow_nonce,
        } = proof;

        // make sure AIR and proof base fields are the same
        if E::BaseField::get_modulus_le_bytes() != context.field_modulus_bytes() {
            return Err(VerifierError::InconsistentBaseField);
        }
        let constraint_frame_width = air.context().num_constraint_composition_columns();

        let num_trace_segments = air.trace_info().num_segments();
        let main_trace_width = air.trace_info().main_trace_width();
        let aux_trace_width = air.trace_info().aux_segment_width();
        let lde_domain_size = air.lde_domain_size();
        let fri_options = air.options().to_fri_options();
        let partition_options = air.options().partition_options();

        // --- parse commitments ------------------------------------------------------------------
        let (trace_commitments, constraint_commitment, fri_commitments) = commitments
            .parse::<H>(num_trace_segments, fri_options.num_fri_layers(lde_domain_size))
            .map_err(|err| VerifierError::ProofDeserializationError(err.to_string()))?;

        // --- parse trace and constraint queries -------------------------------------------------
        let trace_queries =
            TraceQueries::<E, H, V>::new(trace_queries, air, num_unique_queries as usize)?;
        let constraint_queries = ConstraintQueries::<E, H, V>::new(
            constraint_queries,
            air,
            num_unique_queries as usize,
        )?;

        // --- parse FRI proofs -------------------------------------------------------------------
        let fri_num_partitions = fri_proof.num_partitions();
        let fri_remainder = fri_proof
            .parse_remainder()
            .map_err(|err| VerifierError::ProofDeserializationError(err.to_string()))?;
        let (fri_layer_queries, fri_layer_proofs) = fri_proof
            .parse_layers::<E, H, V>(lde_domain_size, fri_options.folding_factor())
            .map_err(|err| VerifierError::ProofDeserializationError(err.to_string()))?;

        // --- parse out-of-domain evaluation frame -----------------------------------------------
        let (ood_trace_frame, ood_constraint_evaluations) = ood_frame
            .parse(main_trace_width, aux_trace_width, constraint_frame_width)
            .map_err(|err| VerifierError::ProofDeserializationError(err.to_string()))?;

        // --- compute the partition size for each trace ------------------------------------------
        let partition_size_main = partition_options
            .partition_size::<E::BaseField>(air.context().trace_info().main_trace_width());
        let partition_size_aux =
            partition_options.partition_size::<E>(air.context().trace_info().aux_segment_width());
        let partition_size_constraint = partition_options
            .partition_size::<E>(air.context().num_constraint_composition_columns());

        Ok(VerifierChannel {
            trace_commitments,
            // trace queries
            trace_queries: Some(trace_queries),
            constraint_commitment,
            // constraint queries
            constraint_queries: Some(constraint_queries),
            // num partitions used in commitment
            partition_size_main,
            partition_size_aux,
            partition_size_constraint,
            // FRI proof
            fri_commitments: Some(fri_commitments),
            fri_layer_proofs,
            fri_layer_queries,
            fri_remainder: Some(fri_remainder),
            fri_num_partitions,
            // out-of-domain evaluation
            ood_trace_frame: Some(ood_trace_frame),
            ood_constraint_evaluations: Some(ood_constraint_evaluations),
            // query seed
            pow_nonce,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_trace_paths_nodes: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_trace_paths_pos: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_comp_paths_nodes: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_comp_paths_pos: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_fri_layer_roots: Vec::new(),
            #[cfg(feature = "pvugc-hooks")]
            pvugc_trace_leaf_digests: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_comp_leaf_digests: None,
            #[cfg(feature = "pvugc-hooks")]
            pvugc_fri_layer_positions: Vec::new(),
            #[cfg(feature = "pvugc-hooks")]
            pvugc_fri_layer_leaf_digests: Vec::new(),
            #[cfg(feature = "pvugc-hooks")]
            pvugc_fri_layer_paths_nodes: Vec::new(),
        })
    }

    // DATA READERS
    // --------------------------------------------------------------------------------------------

    /// Returns execution trace commitments sent by the prover.
    ///
    /// For computations requiring multiple trace segment, the returned slice will contain a
    /// commitment for each trace segment.
    pub fn read_trace_commitments(&self) -> &[H::Digest] {
        &self.trace_commitments
    }

    /// Returns constraint evaluation commitment sent by the prover.
    pub fn read_constraint_commitment(&self) -> H::Digest {
        self.constraint_commitment
    }

    /// Returns trace polynomial evaluations at out-of-domain points z and z * g, where g is the
    /// generator of the trace domain.
    ///
    /// For computations requiring multiple trace segments, evaluations of auxiliary trace
    /// polynomials are also included.
    pub fn read_ood_trace_frame(&mut self) -> TraceOodFrame<E> {
        self.ood_trace_frame.take().expect("already read")
    }

    /// Returns evaluations of composition polynomial columns at z and z * g, where z is
    /// the out-of-domain point, and g is the generator of the trace domain.
    pub fn read_ood_constraint_frame(&mut self) -> QuotientOodFrame<E> {
        self.ood_constraint_evaluations.take().expect("already read")
    }

    /// Returns query proof-of-work nonce sent by the prover.
    pub fn read_pow_nonce(&self) -> u64 {
        self.pow_nonce
    }

    /// Returns trace states at the specified positions of the LDE domain. This also checks if
    /// the trace states are valid against the trace commitment sent by the prover.
    ///
    /// For computations requiring multiple trace segments, trace states for auxiliary segments
    /// are also included as the second value of the returned tuple (trace states for all auxiliary
    /// segments are merged into a single table). Otherwise, the second value is None.
    #[allow(clippy::type_complexity)]
    pub fn read_queried_trace_states(
        &mut self,
        positions: &[usize],
    ) -> Result<(Table<E::BaseField>, Option<Table<E>>), VerifierError> {
        let mut queries = self.trace_queries.take().expect("already read");

        // make sure the states included in the proof correspond to the trace commitment
        let items: Vec<H::Digest> = queries
            .main_states
            .rows()
            .map(|row| hash_row::<H, E::BaseField>(row, self.partition_size_main))
            .collect();

        <V as VectorCommitment<H>>::verify_many(
            self.trace_commitments[0],
            positions,
            &items,
            &queries.query_proofs[0],
        )
        .map_err(|_| VerifierError::TraceQueryDoesNotMatchCommitment)?;
        #[cfg(feature = "pvugc-hooks")]
        { self.pvugc_trace_leaf_digests = Some(items.clone()); }

        #[cfg(feature = "pvugc-hooks")]
        {
            // Reconstruct individual Merkle openings for each queried position
            let openings: Vec<(H::Digest, Vec<H::Digest>)> = compute_openings_from_batch::<E, H>(&queries.query_proofs[0], &items, positions)?;

            // Compute position bits per query from the leaf index
            let mut paths_nodes: Vec<Vec<H::Digest>> = Vec::with_capacity(openings.len());
            let mut paths_pos: Vec<Vec<bool>> = Vec::with_capacity(openings.len());
            for (i, opening) in openings.iter().enumerate() {
                let sibs: &Vec<H::Digest> = &opening.1;
                let depth: usize = sibs.len();
                let mut idx = positions[i];
                let mut pos_bits = Vec::with_capacity(depth);
                for _ in 0..depth {
                    pos_bits.push((idx & 1) == 1);
                    idx >>= 1;
                }
                paths_nodes.push(sibs.clone());
                paths_pos.push(pos_bits);
            }
            self.pvugc_trace_paths_nodes = Some(paths_nodes);
            self.pvugc_trace_paths_pos = Some(paths_pos);
        }

        // PVUGC: also log main trace leaf digests
        #[cfg(feature = "pvugc-hooks")]
        { self.pvugc_trace_leaf_digests = Some(items.clone()); }

        if let Some(ref aux_states) = queries.aux_states {
            let items: Vec<H::Digest> = aux_states
                .rows()
                .map(|row| hash_row::<H, E>(row, self.partition_size_aux))
                .collect();

            <V as VectorCommitment<H>>::verify_many(
                self.trace_commitments[1],
                positions,
                &items,
                &queries.query_proofs[1],
            )
            .map_err(|_| VerifierError::TraceQueryDoesNotMatchCommitment)?;
        }

        Ok((queries.main_states, queries.aux_states))
    }

    /// Returns constraint evaluations at the specified positions of the LDE domain. This also
    /// checks if the constraint evaluations are valid against the constraint commitment sent by
    /// the prover.
    pub fn read_constraint_evaluations(
        &mut self,
        positions: &[usize],
    ) -> Result<Table<E>, VerifierError> {
        let queries = self.constraint_queries.take().expect("already read");

        let items: Vec<H::Digest> = queries
            .evaluations
            .rows()
            .map(|row| hash_row::<H, E>(row, self.partition_size_constraint))
            .collect();

        <V as VectorCommitment<H>>::verify_many(
            self.constraint_commitment,
            positions,
            &items,
            &queries.query_proofs,
        )
        .map_err(|_| VerifierError::ConstraintQueryDoesNotMatchCommitment)?;
        #[cfg(feature = "pvugc-hooks")]
        { self.pvugc_comp_leaf_digests = Some(items.clone()); }

        #[cfg(feature = "pvugc-hooks")]
        {
            // Reconstruct per-query Merkle openings for composition
            let openings: Vec<(H::Digest, Vec<H::Digest>)> = compute_openings_from_batch::<E, H>(&queries.query_proofs, &items, positions)?;
            let mut paths_nodes: Vec<Vec<H::Digest>> = Vec::with_capacity(openings.len());
            let mut paths_pos: Vec<Vec<bool>> = Vec::with_capacity(openings.len());
            for (i, opening) in openings.iter().enumerate() {
                let sibs: &Vec<H::Digest> = &opening.1;
                let depth: usize = sibs.len();
                let mut idx = positions[i];
                let mut pos_bits = Vec::with_capacity(depth);
                for _ in 0..depth {
                    pos_bits.push((idx & 1) == 1);
                    idx >>= 1;
                }
                paths_nodes.push(sibs.clone());
                paths_pos.push(pos_bits);
            }
            self.pvugc_comp_paths_nodes = Some(paths_nodes);
            self.pvugc_comp_paths_pos = Some(paths_pos);
        }

        // PVUGC: also log composition leaf digests
        #[cfg(feature = "pvugc-hooks")]
        { self.pvugc_comp_leaf_digests = Some(items.clone()); }

        Ok(queries.evaluations)
    }
}

// FRI VERIFIER CHANNEL IMPLEMENTATION
// ================================================================================================

impl<E, H, V> FriVerifierChannel<E> for VerifierChannel<E, H, V>
where
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
{
    type Hasher = H;
    type VectorCommitment = V;
    fn read_layer_queries<const N: usize>(
        &mut self,
        positions: &[usize],
        commitment: &<Self::Hasher as crypto::Hasher>::Digest,
    ) -> Result<Vec<[E; N]>, fri::VerifierError> {
        let layer_proof = self.take_next_fri_layer_proof();
        let layer_queries = self.take_next_fri_layer_queries();
        let leaf_values = utils::group_slice_elements(&layer_queries);
        let hashed_values: Vec<<Self::Hasher as crypto::Hasher>::Digest> = leaf_values
            .iter()
            .map(|seg| <Self::Hasher as crypto::ElementHasher>::hash_elements(seg))
            .collect();
        <V as crypto::VectorCommitment<Self::Hasher>>::verify_many(
            *commitment,
            positions,
            &hashed_values,
            &layer_proof,
        )
        .map_err(|_| fri::VerifierError::LayerCommitmentMismatch)?;

        #[cfg(feature = "pvugc-hooks")]
        {
            self.pvugc_fri_layer_positions.push(positions.to_vec());
            self.pvugc_fri_layer_leaf_digests.push(hashed_values.clone());
        }

        Ok(leaf_values.to_vec())
    }

    fn read_fri_num_partitions(&self) -> usize {
        self.fri_num_partitions
    }

    fn read_fri_layer_commitments(&mut self) -> Vec<H::Digest> {
        let v = self.fri_commitments.take().expect("already read");
        #[cfg(feature = "pvugc-hooks")]
        { self.pvugc_fri_layer_roots = v.clone(); }
        v
    }

    fn take_next_fri_layer_proof(&mut self) -> V::MultiProof {
        self.fri_layer_proofs.remove(0)
    }

    fn take_next_fri_layer_queries(&mut self) -> Vec<E> {
        self.fri_layer_queries.remove(0)
    }

    fn take_fri_remainder(&mut self) -> Vec<E> {
        self.fri_remainder.take().expect("already read")
    }
}

// TRACE QUERIES
// ================================================================================================

/// Container of trace query data, including:
/// * Queried states for all trace segments.
/// * Batch opening proof for all queries.
///
/// Trace states for all auxiliary segments are stored in a single table.
struct TraceQueries<
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
> {
    query_proofs: Vec<V::MultiProof>,
    main_states: Table<E::BaseField>,
    aux_states: Option<Table<E>>,
    _h: PhantomData<H>,
}

impl<E, H, V> TraceQueries<E, H, V>
where
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
{
    /// Parses the provided trace queries into trace states in the specified field and
    /// corresponding batch opening proof.
    pub fn new<A: Air<BaseField = E::BaseField>>(
        mut queries: Vec<Queries>,
        air: &A,
        num_queries: usize,
    ) -> Result<Self, VerifierError> {
        assert_eq!(
            queries.len(),
            air.trace_info().num_segments(),
            "expected {} trace segment queries, but received {}",
            air.trace_info().num_segments(),
            queries.len()
        );

        // parse main trace segment queries
        let main_segment_width = air.trace_info().main_trace_width();
        let main_segment_queries = queries.remove(0);
        let (main_segment_query_proofs, main_segment_states) = main_segment_queries
            .parse::<E::BaseField, H, V>(air.lde_domain_size(), num_queries, main_segment_width)
            .map_err(|err| {
                VerifierError::ProofDeserializationError(format!(
                    "main trace segment query deserialization failed: {err}"
                ))
            })?;

        // all query proofs will be aggregated into a single vector
        let mut query_proofs = vec![main_segment_query_proofs];

        // parse auxiliary trace segment queries (if any), and merge resulting tables into a
        // single table
        let aux_trace_states = if air.trace_info().is_multi_segment() {
            let mut aux_trace_states = Vec::new();
            let segment_queries = queries.remove(0);
            let segment_width = air.trace_info().get_aux_segment_width();
            let (segment_query_proof, segment_trace_states) = segment_queries
                .parse::<E, H, V>(air.lde_domain_size(), num_queries, segment_width)
                .map_err(|err| {
                    VerifierError::ProofDeserializationError(format!(
                        "auxiliary trace segment query deserialization failed: {err}"
                    ))
                })?;

            query_proofs.push(segment_query_proof);
            aux_trace_states.push(segment_trace_states);

            // merge tables for each auxiliary segment into a single table
            Some(Table::merge(aux_trace_states))
        } else {
            None
        };

        Ok(Self {
            query_proofs,
            main_states: main_segment_states,
            aux_states: aux_trace_states,
            _h: PhantomData,
        })
    }
}

// CONSTRAINT QUERIES
// ================================================================================================

/// Container of constraint evaluation query data, including:
/// * Queried constraint evaluation values.
/// * Batch opening proof for all queries.
struct ConstraintQueries<
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
> {
    query_proofs: V::MultiProof,
    evaluations: Table<E>,
    _h: PhantomData<H>,
}

impl<E, H, V> ConstraintQueries<E, H, V>
where
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
    V: VectorCommitment<H>,
{
    /// Parses the provided constraint queries into evaluations in the specified field and
    /// corresponding batch opening proof.
    pub fn new<A: Air<BaseField = E::BaseField>>(
        queries: Queries,
        air: &A,
        num_queries: usize,
    ) -> Result<Self, VerifierError> {
        let constraint_frame_width = air.context().num_constraint_composition_columns();

        let (query_proofs, evaluations) = queries
            .parse::<E, H, V>(air.lde_domain_size(), num_queries, constraint_frame_width)
            .map_err(|err| {
                VerifierError::ProofDeserializationError(format!(
                    "constraint evaluation query deserialization failed: {err}"
                ))
            })?;

        Ok(Self {
            query_proofs,
            evaluations,
            _h: PhantomData,
        })
    }
}

// HELPER
// ================================================================================================

/// Hashes a row of a trace in batches where each batch is of size at most `partition_size`.
fn hash_row<H, E>(row: &[E], partition_size: usize) -> H::Digest
where
    E: FieldElement,
    H: ElementHasher<BaseField = E::BaseField>,
{
    if partition_size == row.len() {
        H::hash_elements(row)
    } else {
        let num_partitions = row.len().div_ceil(partition_size);

        let mut buffer = vec![H::Digest::default(); num_partitions];

        row.chunks(partition_size)
            .zip(buffer.iter_mut())
            .for_each(|(chunk, buf)| *buf = H::hash_elements(chunk));
        H::merge_many(&buffer)
    }
}
