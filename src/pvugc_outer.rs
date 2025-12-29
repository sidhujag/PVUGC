//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use crate::arming::{ColumnArms, ColumnBases};
use crate::outer_compressed::{
    fr_inner_to_outer_for, InnerProof, InnerScalar, InnerVk, OuterCircuit,
    OuterScalar, RecursionCycle,
};
use crate::ppe::PvugcVk;
use crate::prover_lean::LeanProvingKey;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_groth16::{
    r1cs_to_qap::PvugcReduction, Groth16, ProvingKey as Groth16PK, VerifyingKey as Groth16VK,
};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::time::Instant;

type StatementVec<C> = Vec<InnerScalar<C>>;

/// Build PVUGC VK and Lean PK from the OUTER proving key.
///
/// IMPORTANT: When the Groth16 verifier gadget is enabled in the outer circuit,
/// the q_const computation needs to generate valid inner proofs for each sampled
/// statement. This requires the inner proving key.
///
/// The `inner_proof_generator` closure takes a vector of statement values (one per
/// public input) and returns a valid inner Groth16 proof for that statement.
/// This ensures the outer circuit's verifier constraints are satisfied during
/// q_const computation.
pub fn build_pvugc_setup_from_pk_for<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
) -> (PvugcVk<C::OuterE>, LeanProvingKey<C::OuterE>)
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let n_inner_inputs = vk_inner.gamma_abc_g1.len() - 1;
    let canonical_samples = canonical_sample_statements::<C>(n_inner_inputs);
    build_pvugc_setup_from_pk_for_with_samples::<C, F>(
        pk_outer,
        vk_inner,
        inner_proof_generator,
        canonical_samples,
    )
}

pub fn build_pvugc_setup_from_pk_for_with_samples<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
    sample_statements: Vec<StatementVec<C>>,
) -> (PvugcVk<C::OuterE>, LeanProvingKey<C::OuterE>)
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let start = Instant::now();
    println!("[Setup] Starting PVUGC Setup from PK...");

    let n_inner_inputs = vk_inner.gamma_abc_g1.len() - 1;
    println!(
        "[Setup] Inner public inputs (packed outer instances): {}",
        n_inner_inputs
    );
    assert_eq!(
        sample_statements.len(),
        n_inner_inputs + 1,
        "sample statements must provide n+1 entries"
    );

    // Sanitize cycle name for filename and derive a hash of the verifying key (circuit)
    // so caches from different circuits never collide.
    let safe_name = C::name().replace('/', "_").replace(' ', "_");
    let cache_path = format!("outer_lean_setup_pk_vk_{}.bin", safe_name);

    let cache_file = std::path::Path::new(&cache_path);
    let (lean_pk, t_const_gt) = if cache_file.exists() {
        println!("[Setup] Found cached setup at {}, loading...", cache_path);
        let file = File::open(&cache_path).expect("failed to open cached setup");
        let reader = BufReader::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        let (pk, t_gt): (
            LeanProvingKey<C::OuterE>,
            Vec<PairingOutput<C::OuterE>>,
        ) = CanonicalDeserialize::deserialize_uncompressed_unchecked(reader)
            .expect("failed to deserialize setup");
        println!("[Setup] Cached setup loaded in {:?}", start.elapsed());
        (pk, t_gt)
    } else {
        println!("[Setup] No cache found. Computing witness bases...");
        let wb_result = compute_witness_bases::<C>(pk_outer, vk_inner, n_inner_inputs);
        println!("[Setup] Witness Bases Computed in {:?}", start.elapsed());

        audit_witness_bases::<C>(&wb_result, pk_outer.vk.gamma_abc_g1.len());
        
        let lean_pk = LeanProvingKey {
            vk: pk_outer.vk.clone(),
            beta_g1: pk_outer.beta_g1,
            delta_g1: pk_outer.delta_g1,
            a_query_wit: {
                let q = pk_outer.a_query.clone();
                let num_public = pk_outer.vk.gamma_abc_g1.len();
                for i in 1..num_public {
                    if i < q.len() {
                        assert!(
                            q[i].is_zero(),
                            "[SECURITY AUDIT FAIL] a_query has non-zero public handle at index {}. \
                             Expected a_query[1..num_public) to be zero (public-in-C-only).",
                            i
                        );
                    }
                }
                q
            },
            b_g1_query: pk_outer.b_g1_query.clone(),
            b_g2_query: pk_outer.b_g2_query.clone(),
            h_query_wit: wb_result.h_query_wit,
            l_query: pk_outer.l_query.clone(),
        };

        // Gap-preimage audit: since LeanProvingKey is public in your WE deployment, we
        // additionally guard against accidentally publishing the exact omitted (0,j) gap handles
        // through some other query vector.
        audit_gap_preimages_not_directly_published::<C>(&lean_pk, &wb_result.omitted_gap_bases);

        // Pre-serialization audit: ensure the exact lean CRS view we will serialize/publish
        // contains no forbidden public handles or forbidden basis categories.
        let num_public = lean_pk.vk.gamma_abc_g1.len(); // includes constant "1" at index 0
        for (i, g) in lean_pk.a_query_wit.iter().enumerate().take(num_public).skip(1) {
            assert!(
                g.is_zero(),
                "[SECURITY AUDIT FAIL] LeanProvingKey leaks A-query public handle at index {}.",
                i
            );
        }
        for &(i, j, base) in &lean_pk.h_query_wit {
            let i_idx = i as usize;
            let j_idx = j as usize;
            assert!(
                !base.is_zero(),
                "[SECURITY AUDIT FAIL] h_query_wit contains a zero base at ({}, {}).",
                i,
                j
            );
            // For publication, forbid referencing any public column index (excluding const 0).
            if (i_idx > 0 && i_idx < num_public) || (j_idx > 0 && j_idx < num_public) {
                panic!(
                    "[SECURITY AUDIT FAIL] h_query_wit contains a public-index pair ({}, {}). \
                     Public indices (1..num_public) must not appear in published witness bases.",
                    i,
                    j
                );
            }
            if i_idx == 0 && j_idx == 0 {
                panic!("[SECURITY AUDIT FAIL] h_query_wit contains forbidden (0,0) const×const basis.");
            }
        }

        println!("[Setup] Computing q_points from gap (using custom samples)...");
        let t_const_gt = compute_t_const_points_gt_from_gap::<C, F>(
            pk_outer,
            &lean_pk,
            vk_inner,
            &sample_statements,
            &inner_proof_generator,
        );
        println!("[Setup] t_const_points_gt computed in {:?}", start.elapsed());
        println!("[Setup] Serializing setup to {}...", cache_path);
        let file = File::create(&cache_path).expect("failed to create cache file");
        let mut writer = BufWriter::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        (lean_pk.clone(), t_const_gt.clone())
            .serialize_uncompressed(&mut writer)
            .expect("failed to serialize setup");
        writer.flush().expect("failed to flush buffer");
        (lean_pk, t_const_gt)
    };

    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        t_const_gt,
    );

    println!("[Setup] Complete.");
    (pvugc_vk, lean_pk)
}

pub fn build_pvugc_vk_outer_from_pk_for<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
) -> PvugcVk<C::OuterE>
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    build_pvugc_setup_from_pk_for::<C, F>(pk_outer, vk_inner, inner_proof_generator).0
}

pub fn build_column_bases_outer_for<C: RecursionCycle>(
    pvugc_vk: &PvugcVk<C::OuterE>,
    vk_outer: &Groth16VK<C::OuterE>,
    public_inputs_outer: &[OuterScalar<C>],
) -> ColumnBases<C::OuterE> {
    crate::api::OneSidedPvugc::build_column_bases(pvugc_vk, vk_outer, public_inputs_outer)
        .expect("outer statement should satisfy PVUGC invariants")
}

/// Result of computing witness bases
struct WitnessBasesResult<E: Pairing> {
    /// Sparse H_{ij} bases for witness terms (off-diagonal and diagonal contributions)
    pub h_query_wit: Vec<(u32, u32, E::G1Affine)>,
    /// The omitted "gap preimage" bases (const×wit) for witness columns that touch public-C
    /// binding rows. These are intentionally NOT published, but we compute them during setup
    /// to audit that they do not appear verbatim among any other published G1 handles.
    ///
    /// Important: this is NOT a full "not-in-span" proof (which would require trapdoor /
    /// representation data). It is a strong direct-publication regression guard.
    pub omitted_gap_bases: Vec<(u32, u32, E::G1Affine)>,
}

fn compute_witness_bases<C: RecursionCycle>(
    pk: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    n_inner_inputs: usize,
) -> WitnessBasesResult<C::OuterE> {
    let start = Instant::now();
    println!("[Quotient] Synthesizing Circuit...");

    let dummy_x = vec![InnerScalar::<C>::from(0u64); n_inner_inputs];
    let dummy_proof = crate::outer_compressed::InnerProof::<C> {
        a: Default::default(),
        b: Default::default(),
        c: Default::default(),
    };
    let circuit = OuterCircuit::<C>::new(vk_inner.clone(), dummy_x, dummy_proof);

    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit
        .generate_constraints(cs.clone())
        .expect("synthesis failed");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrix extraction failed");

    // CRITICAL: Domain size must match standard Groth16!
    // Standard Groth16 uses domain of size (num_constraints + num_inputs) to include
    // the "copy constraints" that encode public inputs into the A polynomial.
    let num_constraints = cs.num_constraints();
    let num_inputs = cs.num_instance_variables(); // includes constant 1
    let qap_domain_size = num_constraints + num_inputs;

    let domain = GeneralEvaluationDomain::<OuterScalar<C>>::new(qap_domain_size)
        .or_else(|| {
            GeneralEvaluationDomain::<OuterScalar<C>>::new(qap_domain_size.next_power_of_two())
        })
        .expect("domain creation failed");
    let domain_size = domain.size();

    println!(
        "[Quotient] Matrix extracted ({} constraints + {} inputs = {} QAP size). Domain size: {}. Time: {:?}",
        num_constraints,
        num_inputs,
        qap_domain_size,
        domain_size,
        start.elapsed()
    );

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a = vec![Vec::new(); num_vars];
    let mut col_b = vec![Vec::new(); num_vars];

    // Process constraint rows from matrices
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_a[col].push((row, val));
            }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_b[col].push((row, val));
            }
        }
    }


    println!("[Quotient] Converting SRS to Lagrange Basis (Parallel Group IFFT)....");
    let fft_start = Instant::now();
    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, <C::OuterE as Pairing>::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    let mut lagrange_srs = h_query_proj;
    parallel_ifft_g1(&mut lagrange_srs, &domain);
    let lagrange_srs: Vec<_> = lagrange_srs
        .into_par_iter()
        .map(|p| p.into_affine())
        .collect();
    println!(
        "[Quotient] Lagrange SRS computed in {:?}",
        fft_start.elapsed()
    );

    let num_pub = cs.num_instance_variables();

    // Identify the single witness columns that appear in B on the public-input binding row(s).
    //
    // After the OuterCircuit refactor, each public input x_pub is bound via a constraint:
    //   1 * x_wit = x_pub
    // which places:
    //   - x_pub (public) in C on some row r,
    //   - x_wit (witness) in B on that same row r,
    //   - and the constant ONE wire in A.
    //
    // Publishing the const×wit quotient bases H_{0, x_wit} for those rows would give the
    // adversary a /δ-direction handle with support on the public-C row. We therefore omit
    // exactly those (0, x_wit) pairs from the Lean CRS and rely on the standard–lean C-gap
    // machinery to bake their (statement-dependent, witness-independent) GT effect into
    // t_const_points_gt.
    let mut omit_const_wit_cols: HashSet<usize> = HashSet::new();
    if num_pub > 1 {
        for pub_col in 1..num_pub {
            // Find rows where this public column appears in C.
            // We expect exactly one such row per public input under the binding architecture.
            let mut c_rows: Vec<usize> = Vec::new();
            for (row, terms) in matrices.c.iter().enumerate() {
                if row >= domain_size {
                    continue;
                }
                if terms.iter().any(|&(_, col)| col == pub_col) {
                    c_rows.push(row);
                }
            }
            for &row in &c_rows {
                // Collect witness columns that appear in B on this row.
                let b_wit_cols: Vec<usize> = matrices.b[row]
                    .iter()
                    .filter_map(|&(_, col)| if col >= num_pub { Some(col) } else { None })
                    .collect();
                // Heuristic (tight for our intended binding row): exactly one witness col in B.
                if b_wit_cols.len() == 1 {
                    omit_const_wit_cols.insert(b_wit_cols[0]);
                }
            }
        }
    }
    if !omit_const_wit_cols.is_empty() {
        println!(
            "[Quotient] Omitting {} (const,wit) columns touching public-C binding row(s): {:?}",
            omit_const_wit_cols.len(),
            omit_const_wit_cols.iter().take(8).collect::<Vec<_>>()
        );
    }

    let mut vars_a = HashSet::new();
    let mut vars_b = HashSet::new();
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_a.insert(col);
            }
        }
    }

    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_b.insert(col);
            }
        }
    }

    let mut active_pairs = HashSet::new();

    for &i in &vars_a {
        for &j in &vars_b {
            if i < num_pub && j < num_pub {
                continue;
            }
            // Critical hardening: omit const×wit bases that touch public-C binding rows.
            if i == 0 && omit_const_wit_cols.contains(&j) {
                continue;
            }
            active_pairs.insert((i, j));
        }
    }

    // Estimate max capacity needed for buffers to avoid reallocation in hot loop
    // Most pairs are sparse-sparse, but dense-sparse pairs (involving one_var) need large buffers.
    // We assume max_sparse ~ 10 (typical R1CS).
    // Safe upper bound: max(dense_A * 10, dense_B * 10).
    let max_col_a = col_a.iter().map(|c| c.len()).max().unwrap_or(0);
    let max_col_b = col_b.iter().map(|c| c.len()).max().unwrap_or(0);
    let buffer_capacity = std::cmp::max(max_col_a, max_col_b) * 20;
    println!(
        "[Quotient] Pre-allocating buffers of size {} to avoid churn",
        buffer_capacity
    );

    // --- Diagonal Terms Computation (Optimized via Convolution) ---
    println!("[Quotient] Computing Diagonal Correction vector Q...");
    let diag_start = Instant::now();

    // We need Q[k] = Q_k(tau) for all k.
    // Q_k(tau) = sum_m C_{k,m} L_m(tau).
    // The matrix C is circulant: C_{k,m} depends on (m-k) mod n.
    // Let u_j = C_{0,j} = Q_0(omega^j).
    // Then Q = u * L (convolution).
    // We compute this via FFT: Q = IFFT( FFT(u) . FFT(L) ).

    let n_field = domain.size_as_field_element();
    let t0 =
        (n_field - OuterScalar::<C>::one()) * (n_field + n_field).inverse().expect("2n invertible");

    // 1. Build kernel u
    let mut u = vec![OuterScalar::<C>::zero(); domain_size];
    u[0] = t0;

    // u[j] = 1 / (n * (1 - omega^j))
    // We need to batch invert.
    let mut denoms = Vec::with_capacity(domain_size - 1);
    let mut indices = Vec::with_capacity(domain_size - 1);

    for j in 1..domain_size {
        let omega_j = domain.element(j);
        let denom = n_field * (OuterScalar::<C>::one() - omega_j);
        denoms.push(denom);
        indices.push(j);
    }

    ark_ff::batch_inversion(&mut denoms);
    for (i, &j) in indices.iter().enumerate() {
        u[j] = denoms[i];
    }

    // For off-diagonal terms we repeatedly need:
    //   inv(n * (ω^k - ω^m)) for k != m
    // Using ω^k - ω^m = ω^m (ω^{k-m} - 1) = -ω^m (1 - ω^{k-m}),
    // we have:
    //   1/(n(ω^k-ω^m)) = -ω^{-m} * 1/(n(1-ω^{k-m})).
    //
    // We already computed inv_n_one_minus_omega[d] = 1/(n(1-ω^d)) as u[d] (time domain).
    // Precompute ω^{-m} as ω^{n-m} in the subgroup (no inversions required).
    let inv_n_one_minus_omega = u.clone();

    // Reverse u[1..] to compute correlation via convolution
    // We want sum_j L_j * u_{j-k} = sum_j L_j * u_{-(k-j)}
    // Convolution computes sum_j L_j * v_{k-j}. So we need v_x = u_{-x}.
    if domain_size > 1 {
        u[1..].reverse();
    }

    // 2. FFT(u)
    parallel_fft_scalar(&mut u, &domain);

    // 3. FFT(L)
    // lagrange_srs is currently [L_0, ..., L_{n-1}].
    // We need to convert to Projective for FFT
    let mut l_fft: Vec<_> = lagrange_srs.iter().map(|p| p.into_group()).collect();
    parallel_fft_g1(&mut l_fft, &domain);

    // 4. Pointwise Product in Frequency Domain
    // Q_hat[i] = u_hat[i] * L_hat[i]
    l_fft
        .par_iter_mut()
        .zip(u.par_iter())
        .for_each(|(l_val, &u_val)| {
            *l_val *= u_val;
        });

    // 5. IFFT to get Q
    parallel_ifft_g1(&mut l_fft, &domain);

    // Convert back to Affine for storage/use
    let q_vector: Vec<_> = l_fft.into_par_iter().map(|p| p.into_affine()).collect();

    println!(
        "[Quotient] Diagonal Q-vector computed in {:?}",
        diag_start.elapsed()
    );

    // --- Main Loop with Q-Vector Support ---
    // We rewrite the main loop to use q_vector for diagonal terms (k==m)

    let wit_start = Instant::now();
    let mut sorted_pairs: Vec<(usize, usize)> = active_pairs.into_iter().collect();
    sorted_pairs.sort();

    let domain_elements: Vec<_> = (0..domain.size()).map(|i| domain.element(i)).collect();
    let inv_domain_elements: Vec<_> = (0..domain.size())
        .map(|i| {
            // ω^{-i} = ω^{n-i} in the multiplicative subgroup (with ω^0 = 1)
            let idx = if i == 0 { 0 } else { domain.size() - i };
            domain_elements[idx]
        })
        .collect();
    let total_pairs = sorted_pairs.len();
    let progress_counter = std::sync::atomic::AtomicUsize::new(0);

    // Chunk size for batching
    const CHUNK_SIZE: usize = 512;

    let h_wit: Vec<_> = sorted_pairs
        .par_chunks(CHUNK_SIZE)
        .flat_map(|chunk| {
            let mut acc_u = Vec::with_capacity(max_col_a);
            let mut acc_v = Vec::with_capacity(max_col_b);
            // Build MSM tasks per pair, then run them in parallel. This preserves high throughput
            // on many-core machines (nested parallelism can help here).
            let mut msm_tasks: Vec<(
                Vec<<C::OuterE as Pairing>::G1Affine>,
                Vec<OuterScalar<C>>,
                (u32, u32),
            )> = Vec::with_capacity(chunk.len());

            for &(i, j) in chunk {
                let prog = progress_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if prog == 0 || prog % 100000 == 0 {
                    let elapsed = wit_start.elapsed().as_secs_f64();
                    let rate = prog as f64 / elapsed;
                    println!(
                        "[Quotient] {}/{} ({:.1}%) | {:.0} pair/s",
                        prog,
                        total_pairs,
                        (prog as f64 / total_pairs as f64) * 100.0,
                        rate
                    );
                }

                let i_idx = i as usize;
                let j_idx = j as usize;
                let rows_u: &Vec<(usize, OuterScalar<C>)> = &col_a[i_idx];
                let rows_v: &Vec<(usize, OuterScalar<C>)> = &col_b[j_idx];

                if rows_u.is_empty() || rows_v.is_empty() {
                    continue;
                }

                let n_u = rows_u.len();
                let n_v = rows_v.len();

                // 1. Accumulate coefficients
                acc_u.clear();
                acc_u.resize(n_u, OuterScalar::<C>::zero());
                acc_v.clear();
                acc_v.resize(n_v, OuterScalar::<C>::zero());

                // Extra bases for diagonal contributions (using q_vector)
                // We may encounter multiple diagonal hits (k==m) per (i,j). Aggregate them by k so each
                // q_vector[k] appears at most once in the MSM (reduces MSM size noticeably for dense overlaps).
                let mut diag_terms: Vec<(usize, OuterScalar<C>)> = Vec::new();
                diag_terms.reserve(std::cmp::min(n_u, n_v));

                for (idx_u, &(_, val_u)) in rows_u.iter().enumerate() {
                    for (idx_v, &(_, val_v)) in rows_v.iter().enumerate() {
                        let k = rows_u[idx_u].0;
                        let m = rows_v[idx_v].0;

                        let prod = val_u * val_v;

                        if k == m {
                            // Diagonal term: prod * Q[k]
                            diag_terms.push((k, prod));
                        } else {
                            // Off-diagonal term
                            let wm = domain_elements[m];
                            let wk = domain_elements[k];
                            // inv(n*(wk-wm)) = -ω^{-m} * inv_n_one_minus_omega[(k-m) mod n]
                            let d = if k >= m { k - m } else { k + domain_size - m };
                            // inv_n_one_minus_omega[0] is special and not used here because k != m ⇒ d != 0.
                            let inv_denom = -(inv_domain_elements[m] * inv_n_one_minus_omega[d]);
                            let common = prod * inv_denom;
                            acc_u[idx_u] += common * wm;
                            acc_v[idx_v] -= common * wk;
                        }
                    }
                }

                // 3. Collect bases for MSM
                let mut pair_bases =
                    Vec::with_capacity(max_col_a + max_col_b + diag_terms.len());
                let mut pair_scalars =
                    Vec::with_capacity(max_col_a + max_col_b + diag_terms.len());

                // Add off-diagonal contributions (Lagrange bases)
                for (idx_u, &(k, _)) in rows_u.iter().enumerate() {
                    if !acc_u[idx_u].is_zero() {
                        pair_bases.push(lagrange_srs[k]);
                        pair_scalars.push(acc_u[idx_u]);
                    }
                }
                for (idx_v, &(m, _)) in rows_v.iter().enumerate() {
                    if !acc_v[idx_v].is_zero() {
                        pair_bases.push(lagrange_srs[m]);
                        pair_scalars.push(acc_v[idx_v]);
                    }
                }

                // Add diagonal contributions (Q bases)
                if !diag_terms.is_empty() {
                    diag_terms.sort_unstable_by_key(|(k, _)| *k);
                    let mut cur_k = diag_terms[0].0;
                    let mut cur_acc = OuterScalar::<C>::zero();
                    for (k, s) in diag_terms.into_iter() {
                        if k != cur_k {
                            if !cur_acc.is_zero() {
                                pair_bases.push(q_vector[cur_k]);
                                pair_scalars.push(cur_acc);
                            }
                            cur_k = k;
                            cur_acc = s;
                        } else {
                            cur_acc += s;
                        }
                    }
                    if !cur_acc.is_zero() {
                        pair_bases.push(q_vector[cur_k]);
                        pair_scalars.push(cur_acc);
                    }
                }

                if !pair_bases.is_empty() {
                    msm_tasks.push((pair_bases, pair_scalars, (i as u32, j as u32)));
                }
            }

            // Process MSMs in parallel for this chunk.
            let msm_results: Vec<((u32, u32), <C::OuterE as Pairing>::G1)> = msm_tasks
                .into_par_iter()
                .map(|(bases, scalars, pair_id)| {
                    let h_acc = <C::OuterE as Pairing>::G1::msm(&bases, &scalars).unwrap();
                    (pair_id, h_acc)
                })
                .filter(|(_, h_acc)| !h_acc.is_zero())
                .collect();

            let mut point_accs = Vec::with_capacity(msm_results.len());
            let mut point_ids = Vec::with_capacity(msm_results.len());
            for (pair_id, h_acc) in msm_results {
                point_accs.push(h_acc);
                point_ids.push(pair_id);
            }

            let mut affine_results = Vec::with_capacity(point_accs.len());
            if !point_accs.is_empty() {
                let affines = <C::OuterE as Pairing>::G1::normalize_batch(&point_accs);
                for (idx, affine) in affines.into_iter().enumerate() {
                    affine_results.push((point_ids[idx].0, point_ids[idx].1, affine));
                }
            }

            affine_results
        })
        .collect();
    let count = h_wit.len();
    println!(
        "[Quotient] Witness Bases done. Found {} non-zero bases. Time: {:?}",
        count,
        wit_start.elapsed()
    );

    // Post-compute audit: ensure our omission rule actually took effect.
    //
    // We intentionally omit (const,wit) bases (0, j) for witness columns `j` that touch the
    // public-input binding row(s). If these pairs appear here, then the lean CRS would include
    // the very bases we meant to bake via the standard–lean C-gap machinery.
    if !omit_const_wit_cols.is_empty() {
        let mut offenders: Vec<(u32, u32)> = Vec::new();
        for &(i, j, _) in &h_wit {
            if i == 0 && omit_const_wit_cols.contains(&(j as usize)) {
                offenders.push((i, j));
                if offenders.len() >= 8 {
                    break;
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "[SECURITY AUDIT FAIL] Found forbidden (const,wit) quotient bases for omitted witness cols. \
             Expected no (0,j) bases for j in {:?}, but saw examples: {:?}",
            omit_const_wit_cols,
            offenders
        );
    }

    // Compute the omitted gap preimage bases (0,j) as actual points so we can audit that they
    // aren't accidentally published elsewhere (e.g., via A/B/L queries).
    //
    // This is intentionally computed AFTER the parallel h_wit construction: omit_const_wit_cols
    // should be tiny (≈ number of public inputs) so a sequential computation here is fine.
    let mut omitted_gap_bases: Vec<(u32, u32, <C::OuterE as Pairing>::G1Affine)> = Vec::new();
    if !omit_const_wit_cols.is_empty() {
        let mut acc_u: Vec<OuterScalar<C>> = Vec::new();
        let mut acc_v: Vec<OuterScalar<C>> = Vec::new();

        for &j in omit_const_wit_cols.iter() {
            let i_idx = 0usize;
            let j_idx = j;
            if i_idx >= col_a.len() || j_idx >= col_b.len() {
                continue;
            }
            let rows_u: &Vec<(usize, OuterScalar<C>)> = &col_a[i_idx];
            let rows_v: &Vec<(usize, OuterScalar<C>)> = &col_b[j_idx];
            if rows_u.is_empty() || rows_v.is_empty() {
                continue;
            }

            let n_u = rows_u.len();
            let n_v = rows_v.len();
            acc_u.clear();
            acc_u.resize(n_u, OuterScalar::<C>::zero());
            acc_v.clear();
            acc_v.resize(n_v, OuterScalar::<C>::zero());

            let mut diag_terms: Vec<(usize, OuterScalar<C>)> = Vec::new();
            diag_terms.reserve(std::cmp::min(n_u, n_v));

            for (idx_u, &(_, val_u)) in rows_u.iter().enumerate() {
                for (idx_v, &(_, val_v)) in rows_v.iter().enumerate() {
                    let k = rows_u[idx_u].0;
                    let m = rows_v[idx_v].0;
                    let prod = val_u * val_v;
                    if k == m {
                        diag_terms.push((k, prod));
                    } else {
                        let wm = domain_elements[m];
                        let wk = domain_elements[k];
                        let d = if k >= m { k - m } else { k + domain_size - m };
                        let inv_denom = -(inv_domain_elements[m] * inv_n_one_minus_omega[d]);
                        let common = prod * inv_denom;
                        acc_u[idx_u] += common * wm;
                        acc_v[idx_v] -= common * wk;
                    }
                }
            }

            let mut bases: Vec<<C::OuterE as Pairing>::G1Affine> =
                Vec::with_capacity(n_u + n_v + diag_terms.len());
            let mut scalars: Vec<OuterScalar<C>> = Vec::with_capacity(n_u + n_v + diag_terms.len());

            for (idx_u, &(k, _)) in rows_u.iter().enumerate() {
                if !acc_u[idx_u].is_zero() {
                    bases.push(lagrange_srs[k]);
                    scalars.push(acc_u[idx_u]);
                }
            }
            for (idx_v, &(m, _)) in rows_v.iter().enumerate() {
                if !acc_v[idx_v].is_zero() {
                    bases.push(lagrange_srs[m]);
                    scalars.push(acc_v[idx_v]);
                }
            }

            if !diag_terms.is_empty() {
                diag_terms.sort_unstable_by_key(|(k, _)| *k);
                let mut cur_k = diag_terms[0].0;
                let mut cur_acc = OuterScalar::<C>::zero();
                for (k, s) in diag_terms.into_iter() {
                    if k != cur_k {
                        if !cur_acc.is_zero() {
                            bases.push(q_vector[cur_k]);
                            scalars.push(cur_acc);
                        }
                        cur_k = k;
                        cur_acc = s;
                    } else {
                        cur_acc += s;
                    }
                }
                if !cur_acc.is_zero() {
                    bases.push(q_vector[cur_k]);
                    scalars.push(cur_acc);
                }
            }

            if bases.is_empty() {
                continue;
            }

            let h_acc = <C::OuterE as Pairing>::G1::msm(&bases, &scalars).unwrap();
            if h_acc.is_zero() {
                continue;
            }
            omitted_gap_bases.push((0u32, j as u32, h_acc.into_affine()));
        }
    }

    WitnessBasesResult {
        h_query_wit: h_wit,
        omitted_gap_bases,
    }
}
// --- Group FFT Helpers ---

fn parallel_fft_scalar<F: PrimeField>(a: &mut [F], domain: &GeneralEvaluationDomain<F>) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();

    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
    }

    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));

        // chunk_size = 2*m
        // We can process in parallel if chunks are large enough
        // For scalars, rayon might add overhead for small chunks, but let's stick to pattern
        a.par_chunks_mut(2 * m).for_each(|chunk| {
            let mut w = F::one();
            for j in 0..m {
                let t = chunk[j + m] * w;
                let u = chunk[j];
                chunk[j] = u + t;
                chunk[j + m] = u - t;
                w *= omega_m;
            }
        });
        m *= 2;
    }
}

fn audit_witness_bases<C: RecursionCycle>(
    wb: &WitnessBasesResult<C::OuterE>,
    num_public: usize,
) {
    // 1. Check for pure public pairs in h_query_wit
    for &(i, j, _) in &wb.h_query_wit {
        let i_idx = i as usize;
        let j_idx = j as usize;
        let pure_public =
            i_idx > 0 && i_idx < num_public && j_idx > 0 && j_idx < num_public;
        assert!(
            !pure_public,
            "h_query_wit leaked pure public pair ({}, {})",
            i,
            j
        );
        
        // 2. Check that public inputs (columns 1..num_public) do NOT appear in A-side (index i),
        //    matching the "public in C only" architecture used in the security docs.
        // In h_query_wit(i, j), 'i' corresponds to the A-matrix variable and 'j' to the B-matrix
        // variable in the product a_i * b_j. Our secure outer circuit binds public inputs via
        //   1 * reconstructed(bits) = x_pub
        // which places x_pub only in the C-matrix. The 1-wire (index 0) lives in A, but the
        // actual public columns (1..num_public) must be A-free.
        // We therefore forbid 'i' being a public input index (1..num_public); if it is, a public
        // input appeared in A, violating u_pub = 0.
        if i_idx > 0 && i_idx < num_public {
             panic!(
                "[SECURITY AUDIT FAIL] Public input column {} found in Matrix A (via pair {}, {}). \
                 Public inputs must only appear in Matrix B (One-Sided Property).",
                i_idx, i, j
            );
        }
    }
    
    // 3. Quotient Reachability Check - verify Q_pub is unreachable from h_query_wit span
    // This confirms the "baked quotient in GT can't be ρ-exponentiated" security property.
    println!("\n--- Quotient Reachability Check ---");
    
    let mut const_const_count = 0usize;
    let mut wit_wit_count = 0usize;
    let mut const_wit_count = 0usize;
    let mut wit_const_count = 0usize;
    let mut wit_pub_count = 0usize;
    let mut pub_wit_count = 0usize;
    
    for &(i, j, _) in &wb.h_query_wit {
        let i_idx = i as usize;
        let j_idx = j as usize;
        
        let i_is_const = i_idx == 0;
        let i_is_pub = i_idx > 0 && i_idx < num_public;
        let i_is_wit = i_idx >= num_public;
        
        let j_is_const = j_idx == 0;
        let j_is_pub = j_idx > 0 && j_idx < num_public;
        let j_is_wit = j_idx >= num_public;
        
        if i_is_const && j_is_const {
            const_const_count += 1;  // Should never happen - (0,0) is skipped
        } else if i_is_wit && j_is_wit {
            wit_wit_count += 1;
        } else if i_is_const && j_is_wit {
            const_wit_count += 1;
        } else if i_is_wit && j_is_const {
            wit_const_count += 1;
        } else if i_is_wit && j_is_pub {
            wit_pub_count += 1;
        } else if i_is_pub && j_is_wit {
            pub_wit_count += 1;
        }
    }
    
    println!("  h_query_wit composition:");
    println!("    (const, const): {} pairs (should be 0 - skipped for T_const^ρ security)", const_const_count);
    println!("    (const, wit): {} pairs", const_wit_count);
    println!("    (wit, const): {} pairs", wit_const_count);
    println!("    (wit, wit):   {} pairs", wit_wit_count);
    println!("    (wit, pub):   {} pairs (should be 0 for optimal security)", wit_pub_count);
    println!("    (pub, wit):   {} pairs (should be 0 - blocked by A=0 for pub)", pub_wit_count);
    
    // Security check: (wit, pub) pairs could theoretically leak if they exist,
    // but the main audit's "Public columns never share A/B rows" check ensures they're zero bases.
    // Still, we flag them for awareness.
    if wit_pub_count > 0 {
        println!("  ⚠️  WARNING: {} (wit,pub) pairs exist in h_query_wit.", wit_pub_count);
        println!("      These should produce zero bases due to 'no shared A/B rows' property.");
        println!("      Consider filtering them out explicitly for cleaner CRS.");
    }
    
    if pub_wit_count > 0 {
        panic!(
            "[SECURITY AUDIT FAIL] {} (pub,wit) pairs in h_query_wit! \
             Public inputs should have A=0, so these shouldn't exist.",
            pub_wit_count
        );
    }
    
    // Security check: (const, const)
    if const_const_count > 0 {
        panic!(
            "[SECURITY AUDIT FAIL] {} (const,const) pairs in h_query_wit!",
            const_const_count
        );
    }
    
    // Final verdict on quotient reachability
    let only_safe_pairs = pub_wit_count == 0 && const_const_count == 0;
    if only_safe_pairs {
        println!("[PASS] Quotient Reachability: h_query_wit contains clean span.");
    }
}

fn audit_gap_preimages_not_directly_published<C: RecursionCycle>(
    lean_pk: &LeanProvingKey<C::OuterE>,
    omitted_gap_bases: &[(u32, u32, <C::OuterE as Pairing>::G1Affine)],
) {
    use ark_serialize::CanonicalSerialize;

    if omitted_gap_bases.is_empty() {
        return;
    }

    fn key<E: Pairing>(p: &E::G1Affine) -> Vec<u8> {
        let mut out = Vec::new();
        p.serialize_compressed(&mut out)
            .expect("G1 serialize_compressed");
        out
    }

    let mut published: std::collections::HashSet<Vec<u8>> = std::collections::HashSet::new();

    // VK G1 handles
    published.insert(key::<C::OuterE>(&lean_pk.vk.alpha_g1));
    for g in &lean_pk.vk.gamma_abc_g1 {
        published.insert(key::<C::OuterE>(g));
    }

    // Lean PK extra G1 handles
    published.insert(key::<C::OuterE>(&lean_pk.beta_g1));
    published.insert(key::<C::OuterE>(&lean_pk.delta_g1));
    for g in &lean_pk.a_query_wit {
        published.insert(key::<C::OuterE>(g));
    }
    for g in &lean_pk.b_g1_query {
        published.insert(key::<C::OuterE>(g));
    }
    for g in &lean_pk.l_query {
        published.insert(key::<C::OuterE>(g));
    }
    for &(_, _, g) in &lean_pk.h_query_wit {
        published.insert(key::<C::OuterE>(&g));
    }

    // Audit: none of the omitted gap preimages may appear verbatim in the published set.
    let mut offenders: Vec<(u32, u32)> = Vec::new();
    for &(i, j, g) in omitted_gap_bases {
        if published.contains(&key::<C::OuterE>(&g)) {
            offenders.push((i, j));
            if offenders.len() >= 8 {
                break;
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "[SECURITY AUDIT FAIL] Omitted (const,wit) gap preimage bases appear verbatim among published G1 handles. \
         This defeats the T_const barrier. Example offending pairs: {:?}",
        offenders
    );
}

fn parallel_fft_g1<G: CurveGroup<ScalarField = F> + Send, F: PrimeField>(
    a: &mut [G],
    domain: &GeneralEvaluationDomain<F>,
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();

    // Serial bit reverse (fast enough)
    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
    }

    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));

        // Parallel Butterfly
        a.par_chunks_mut(2 * m).for_each(|chunk| {
            let mut w = F::one();
            for j in 0..m {
                let t = chunk[j + m] * w;
                let u = chunk[j];
                chunk[j] = u + t;
                chunk[j + m] = u - t;
                w *= omega_m;
            }
        });
        m *= 2;
    }
}

fn parallel_ifft_g1<G: CurveGroup<ScalarField = F> + Send, F: PrimeField>(
    a: &mut [G],
    domain: &GeneralEvaluationDomain<F>,
) {
    parallel_fft_g1(a, domain);
    if a.len() > 1 {
        a[1..].reverse();
    }
    let n_inv = domain.size_as_field_element().inverse().unwrap();
    // Parallel scaling
    a.par_iter_mut().for_each(|x| *x *= n_inv);
}

/// Compute T_const basis points in GT:
///   T_i = e(Q_i, delta)
/// where Q(x) = Q_0 + Σ x_i Q_i is the *C-gap* between standard and lean Groth16 proofs.
pub fn compute_t_const_points_gt_from_gap<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    lean_pk: &LeanProvingKey<C::OuterE>,
    vk_inner: &InnerVk<C>,
    sample_statements: &[StatementVec<C>],
    inner_proof_generator: &F,
) -> Vec<PairingOutput<C::OuterE>>
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let q_points_g1 = compute_q_const_points_from_gap::<C, F>(
        pk_outer,
        lean_pk,
        vk_inner,
        sample_statements,
        inner_proof_generator,
    );

    let delta_g2 = pk_outer.vk.delta_g2;
    q_points_g1
        .into_iter()
        .map(|q| C::OuterE::pairing(q, delta_g2))
        .collect()
}

/// Compute Q_i in G1 from the standard–lean *C* gap:
///   c_gap(x) := C_std(x) - C_lean(x) = Q(x)
///
/// IMPORTANT: we *assert* A_std == A_lean and B_std == B_lean (no randomizers / no mismatch),
/// otherwise your gap is not the quotient-only delta.
pub fn compute_q_const_points_from_gap<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    lean_pk: &LeanProvingKey<C::OuterE>,
    vk_inner: &InnerVk<C>,
    sample_statements: &[StatementVec<C>],
    inner_proof_generator: &F,
) -> Vec<<C::OuterE as Pairing>::G1Affine>
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    assert!(!sample_statements.is_empty(), "need ≥ 1 sample");
    let n_inner_inputs = sample_statements[0].len();
    for (i, s) in sample_statements.iter().enumerate() {
        assert_eq!(
            s.len(),
            n_inner_inputs,
            "sample {} has wrong length: got {}, expected {}",
            i,
            s.len(),
            n_inner_inputs
        );
    }

    let mut gaps: Vec<(Vec<OuterScalar<C>>, <C::OuterE as Pairing>::G1Affine)> =
        Vec::with_capacity(sample_statements.len());

    for statement in sample_statements {
        // Valid inner proof for THIS statement vector.
        let inner_proof = inner_proof_generator(statement);

        // Standard proof (no-ZK) for the same circuit instance.
        let circuit_std = OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof.clone());
        let proof_std = Groth16::<C::OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            circuit_std,
            pk_outer,
        )
        .expect("standard proof failed");

        // Lean proof with *explicit* r=s=0 (must match standard no-zk shape).
        let circuit_lean = OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof.clone());
        let (proof_lean, _) = crate::prover_lean::prove_lean_with_randomizers(
            lean_pk,
            circuit_lean,
            OuterScalar::<C>::zero(),
            OuterScalar::<C>::zero(),
        )
        .expect("lean proof failed");

        // Guard: A and B must match, otherwise gap includes randomizers or mismatched bases.
        assert_eq!(
            proof_std.a, proof_lean.a,
            "std/lean A mismatch: gap extraction would include randomizer/basis drift"
        );
        assert_eq!(
            proof_std.b, proof_lean.b,
            "std/lean B mismatch: gap extraction would include randomizer/basis drift"
        );

        // The gap lives entirely in C:
        let c_gap = proof_std.c.into_group() - proof_lean.c.into_group();

        // Extract outer circuit public inputs (instance assignment minus constant ONE).
        let circuit_inputs = OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof);
        let cs_inputs = ark_relations::r1cs::ConstraintSystem::<OuterScalar<C>>::new_ref();
        circuit_inputs
            .generate_constraints(cs_inputs.clone())
            .expect("input extraction failed");
        cs_inputs.finalize();

        let mut instance = cs_inputs.borrow().unwrap().instance_assignment.clone();
        let compressed_inputs = instance.split_off(1); // drop constant ONE

        gaps.push((compressed_inputs, c_gap.into_affine()));
    }

    solve_q_const_from_samples::<C>(gaps)
}


pub fn canonical_sample_statements<C: RecursionCycle>(n_inner_inputs: usize) -> Vec<StatementVec<C>> {
    let mut samples = Vec::with_capacity(n_inner_inputs + 1);
    samples.push(vec![InnerScalar::<C>::zero(); n_inner_inputs]);
    for idx in 0..n_inner_inputs {
        let mut statement = vec![InnerScalar::<C>::zero(); n_inner_inputs];
        statement[idx] = InnerScalar::<C>::one();
        samples.push(statement);
    }
    samples
}

/// Solve Q_0..Q_n from samples (x_s, gap_s) where gap_s = Q_0 + Σ x_s[i] Q_{i+1}.
///
/// Fast path: if samples are canonical (0, e1, e2, ...), then:
///   Q_0 = gap(0)
///   Q_{i+1} = gap(e_i) - gap(0)
pub fn solve_q_const_from_samples<C: RecursionCycle>(
    gaps: Vec<(Vec<OuterScalar<C>>, <C::OuterE as Pairing>::G1Affine)>,
) -> Vec<<C::OuterE as Pairing>::G1Affine> {
    assert!(!gaps.is_empty(), "need ≥ 1 sample");
    let n = gaps[0].0.len();
    assert_eq!(
        gaps.len(),
        n + 1,
        "need exactly n+1 samples (canonical) to recover affine Q"
    );

    // Check canonical shape: row0 all zeros; row(i+1) has 1 at i and 0 elsewhere.
    let is_canonical = {
        let row0 = &gaps[0].0;
        if row0.iter().any(|x| !x.is_zero()) {
            false
        } else {
            (0..n).all(|i| {
                let row = &gaps[i + 1].0;
                row.iter().enumerate().all(|(j, v)| {
                    if j == i { *v == OuterScalar::<C>::one() } else { v.is_zero() }
                })
            })
        }
    };

    if is_canonical {
        let gap0 = gaps[0].1.into_group();
        let mut out = Vec::with_capacity(n + 1);
        out.push(gap0.into_affine()); // Q_0
        for i in 0..n {
            let gi = gaps[i + 1].1.into_group();
            out.push((gi - gap0).into_affine()); // Q_{i+1}
        }
        return out;
    }

    // Fallback (generic): solve linear system M * Q = gap.
    let size = n + 1;
    let mut matrix = vec![vec![OuterScalar::<C>::zero(); size]; size];
    for (row, (x, _)) in gaps.iter().enumerate() {
        matrix[row][0] = OuterScalar::<C>::one();
        for (col, value) in x.iter().enumerate() {
            matrix[row][col + 1] = *value;
        }
    }

    let inv = invert_matrix::<C>(matrix);
    let gaps_group: Vec<_> = gaps.iter().map(|(_, gap)| gap.into_group()).collect();

    let mut q_points = Vec::with_capacity(size);
    for row in 0..size {
        let mut acc = <C::OuterE as Pairing>::G1::zero();
        for col in 0..size {
            let coeff = inv[row][col];
            if !coeff.is_zero() {
                acc += gaps_group[col] * coeff;
            }
        }
        q_points.push(acc.into_affine());
    }
    q_points
}

pub fn invert_matrix<C: RecursionCycle>(
    matrix: Vec<Vec<OuterScalar<C>>>,
) -> Vec<Vec<OuterScalar<C>>> {
    let size = matrix.len();
    let mut aug = vec![vec![OuterScalar::<C>::zero(); 2 * size]; size];

    for i in 0..size {
        assert_eq!(matrix[i].len(), size, "non-square matrix");
        for j in 0..size {
            aug[i][j] = matrix[i][j];
        }
        aug[i][size + i] = OuterScalar::<C>::one();
    }

    for col in 0..size {
        let pivot_row = (col..size)
            .find(|&r| !aug[r][col].is_zero())
            .expect("matrix is not invertible");
        if pivot_row != col {
            aug.swap(col, pivot_row);
        }

        let inv_pivot = aug[col][col].inverse().expect("pivot invertible");
        for j in 0..2 * size {
            aug[col][j] *= inv_pivot;
        }

        for row in 0..size {
            if row == col {
                continue;
            }
            let factor = aug[row][col];
            if !factor.is_zero() {
                for j in 0..2 * size {
                    let tmp = aug[col][j] * factor;
                    aug[row][j] -= tmp;
                }
            }
        }
    }

    let mut inv = vec![vec![OuterScalar::<C>::zero(); size]; size];
    for i in 0..size {
        for j in 0..size {
            inv[i][j] = aug[i][size + j];
        }
    }
    inv
}

pub fn compute_r_to_rho_outer_for<C: RecursionCycle>(
    r: &PairingOutput<C::OuterE>,
    rho: &OuterScalar<C>,
) -> PairingOutput<C::OuterE> {
    let r_to_rho = r.0.pow(&rho.into_bigint());
    PairingOutput(r_to_rho)
}

pub fn compute_target_outer_for<C: RecursionCycle>(
    vk_outer: &Groth16VK<C::OuterE>,
    pvugc_vk: &PvugcVk<C::OuterE>,
    public_inputs_inner: &[InnerScalar<C>],
) -> PairingOutput<C::OuterE> {
    let x_outer: Vec<OuterScalar<C>> = public_inputs_inner
        .iter()
        .map(fr_inner_to_outer_for::<C>)
        .collect();

    crate::ppe::compute_baked_target::<C::OuterE>(vk_outer, pvugc_vk, &x_outer)
        .expect("failed to compute baked target")
}

pub fn arm_columns_outer_for<C: RecursionCycle>(
    bases: &ColumnBases<C::OuterE>,
    rho: &OuterScalar<C>,
) -> ColumnArms<C::OuterE> {
    crate::arming::arm_columns(bases, rho).expect("arm_columns failed")
}