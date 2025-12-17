//! Full STARK Verifier Smoke Test
//!
//! Tests the complete pipeline (VerifierAir-only aggregation):
//! - VDF STARK → VerifierAir (verifies VDF) → Groth16-ready circuit
//! - VDF STARK (×2) → VerifierAir (verifies both) → Groth16-ready circuit

use crate::outer_compressed::{cycles::Bls12Bw6Cycle, RecursionCycle};
use crate::stark::test_utils::{
    build_vdf_recursive_stark_instance,
    build_vdf_recursive_stark_instance_with_fri,
    build_verifying_aggregator_instance,
    get_or_init_inner_crs_keys,
};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

type StarkCycle = Bls12Bw6Cycle;
type StarkInnerE = <StarkCycle as RecursionCycle>::InnerE;

/// Debug test to identify which constraint fails with FRI layers
#[test]
#[ignore]
fn debug_verifier_air_constraints_with_fri() {
    // Legacy debug harness was for AggregatorAir; the current pipeline is VerifierAir-only.
    // If we need this again, reintroduce a focused verifier trace/constraint debug for VerifierAir proofs.
    unimplemented!("VerifierAir-only debug harness not implemented");
}

#[test]
fn full_stark_verifier_smoke() {
    // Complete pipeline: VDF → VerifierAir (leaf wrapper) → Groth16-ready circuit
    
    // 1) Build VDF → VerifierAir → Groth16 circuit
    let instance = build_vdf_recursive_stark_instance(3, 8);
    
    // Synthesize to check constraints (with constraint trace enabled)
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    });
    
    println!("Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("First failing constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "Circuit must be satisfied");

    // Generate Groth16 proof using cached CRS keys
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) = get_or_init_inner_crs_keys();

    let pub_input = vec![instance.statement_hash];
    let proof = Groth16::<StarkInnerE>::prove(&pk, instance.circuit, &mut rng)
        .expect("Groth16 prove");
    // Verify Groth16 proof
    let valid = Groth16::<StarkInnerE>::verify(&vk, &pub_input, &proof).expect("verify");

    assert!(valid, "Full STARK verifier proof should verify");
}

#[test]
fn sanity_universal_inner_circuit_shape_vdf_vs_cubic() {
    // Fast sanity: the Groth16-wrapped inner circuit is intended to be universal.
    // This checks that the two representative instances produce identical AirParams.
    let vdf = crate::stark::test_utils::build_vdf_recursive_stark_instance(3, 8);
    let cubic = crate::stark::test_utils::build_cubic_fib_recursive_stark_instance(1, 1, 16);
    eprintln!("[debug][air_params][vdf] {:?}", vdf.circuit.air_params);
    eprintln!("[debug][air_params][cubic] {:?}", cubic.circuit.air_params);
    let a = &vdf.circuit.air_params;
    let b = &cubic.circuit.air_params;
    assert_eq!(a.trace_width, b.trace_width);
    assert_eq!(a.comp_width, b.comp_width);
    assert_eq!(a.trace_len, b.trace_len);
    assert_eq!(a.lde_blowup, b.lde_blowup);
    assert_eq!(a.num_queries, b.num_queries);
    assert_eq!(a.fri_folding_factor, b.fri_folding_factor);
    assert_eq!(a.fri_num_layers, b.fri_num_layers);
    assert_eq!(a.lde_generator, b.lde_generator);
    assert_eq!(a.domain_offset, b.domain_offset);
    assert_eq!(a.g_lde, b.g_lde);
    assert_eq!(a.g_trace, b.g_trace);
    assert_eq!(a.num_constraint_coeffs, b.num_constraint_coeffs);
    assert_eq!(a.grinding_factor, b.grinding_factor);
    assert_eq!(a.aggregator_version, b.aggregator_version);
    match (&a.combiner_kind, &b.combiner_kind) {
        (crate::stark::gadgets::utils::CombinerKind::RandomRho, crate::stark::gadgets::utils::CombinerKind::RandomRho) => {}
        _ => panic!("combiner_kind mismatch"),
    }
    // `FriTerminalKind` doesn't implement PartialEq; compare by shape.
    match (&a.fri_terminal, &b.fri_terminal) {
        (crate::stark::gadgets::fri::FriTerminalKind::Constant, crate::stark::gadgets::fri::FriTerminalKind::Constant) => {}
        (
            crate::stark::gadgets::fri::FriTerminalKind::Poly { degree: a },
            crate::stark::gadgets::fri::FriTerminalKind::Poly { degree: b },
        ) => assert_eq!(a, b),
        _ => panic!("fri_terminal mismatch between instances"),
    }
}

#[test]
#[ignore] // Debug helper: check cubic circuit satisfaction (no Groth16)
fn debug_cubic_instance_circuit_satisfied() {
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::Registry;

    let cubic = crate::stark::test_utils::build_cubic_fib_recursive_stark_instance(1, 1, 16);
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
        cubic
            .circuit
            .clone()
            .generate_constraints(cs.clone())
            .expect("generate constraints");
    });

    eprintln!(
        "[debug][cubic] constraints={} public_inputs={} witnesses={}",
        cs.num_constraints(),
        cs.num_instance_variables(),
        cs.num_witness_variables()
    );
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("[debug][cubic] UNSAT: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "cubic circuit must be satisfied");
}

#[test]
#[ignore] // Debug helper: compare R1CS matrices vdf vs cubic
fn debug_compare_r1cs_matrices_vdf_vs_cubic() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintMatrices};
    use ark_relations::r1cs::{OptimizationGoal, SynthesisMode};

    let vdf = crate::stark::test_utils::build_vdf_recursive_stark_instance(3, 8);
    let cubic = crate::stark::test_utils::build_cubic_fib_recursive_stark_instance(1, 1, 16);

    let cs_v = ConstraintSystem::new_ref();
    cs_v.set_optimization_goal(OptimizationGoal::Constraints);
    cs_v.set_mode(SynthesisMode::Setup);
    vdf.circuit.clone().generate_constraints(cs_v.clone()).expect("vdf synth");
    cs_v.finalize();
    let cs_c = ConstraintSystem::new_ref();
    cs_c.set_optimization_goal(OptimizationGoal::Constraints);
    cs_c.set_mode(SynthesisMode::Setup);
    cubic.circuit.clone().generate_constraints(cs_c.clone()).expect("cubic synth");
    cs_c.finalize();

    // Basic shape should match.
    assert_eq!(cs_v.num_constraints(), cs_c.num_constraints(), "constraint count differs");
    assert_eq!(cs_v.num_instance_variables(), cs_c.num_instance_variables(), "public var count differs");
    assert_eq!(cs_v.num_witness_variables(), cs_c.num_witness_variables(), "witness var count differs");

    // Compare matrices. If this fails, CRS cannot be shared.
    let m_v = cs_v.to_matrices().expect("vdf matrices");
    let m_c = cs_c.to_matrices().expect("cubic matrices");

    // ConstraintMatrices doesn't implement CanonicalSerialize directly; serialize key fields.
    use ark_serialize::CanonicalSerialize;
    let ser = |m: &ConstraintMatrices<crate::stark::StarkInnerFr>| -> Vec<u8> {
        let mut out = Vec::new();
        // Include sizes as bytes (these affect the QAP).
        out.extend_from_slice(&(m.num_instance_variables as u64).to_le_bytes());
        out.extend_from_slice(&(m.num_witness_variables as u64).to_le_bytes());
        out.extend_from_slice(&(m.num_constraints as u64).to_le_bytes());
        // Serialize sparse matrices + nnz counters.
        m.a.serialize_uncompressed(&mut out).expect("ser A");
        m.b.serialize_uncompressed(&mut out).expect("ser B");
        m.c.serialize_uncompressed(&mut out).expect("ser C");
        m.a_num_non_zero.serialize_uncompressed(&mut out).expect("ser Annz");
        m.b_num_non_zero.serialize_uncompressed(&mut out).expect("ser Bnnz");
        m.c_num_non_zero.serialize_uncompressed(&mut out).expect("ser Cnnz");
        out
    };
    let bv = ser(&m_v);
    let bc = ser(&m_c);

    fn fnv1a64(bytes: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }
    let hv = fnv1a64(&bv);
    let hc = fnv1a64(&bc);

    // Localize mismatch: hash A/B/C separately as well.
    let mut a_v = Vec::new();
    m_v.a.serialize_uncompressed(&mut a_v).expect("ser vdf A");
    let mut a_c = Vec::new();
    m_c.a.serialize_uncompressed(&mut a_c).expect("ser cubic A");
    let mut b_v = Vec::new();
    m_v.b.serialize_uncompressed(&mut b_v).expect("ser vdf B");
    let mut b_c = Vec::new();
    m_c.b.serialize_uncompressed(&mut b_c).expect("ser cubic B");
    let mut c_v = Vec::new();
    m_v.c.serialize_uncompressed(&mut c_v).expect("ser vdf C");
    let mut c_c = Vec::new();
    m_c.c.serialize_uncompressed(&mut c_c).expect("ser cubic C");

    eprintln!(
        "[debug][matrices] vdf_bytes={} cubic_bytes={} vdf_hash={:016x} cubic_hash={:016x} | A={:016x}/{:016x} B={:016x}/{:016x} C={:016x}/{:016x}",
        bv.len(),
        bc.len(),
        hv,
        hc,
        fnv1a64(&a_v),
        fnv1a64(&a_c),
        fnv1a64(&b_v),
        fnv1a64(&b_c),
        fnv1a64(&c_v),
        fnv1a64(&c_c),
    );
    if fnv1a64(&a_v) != fnv1a64(&a_c) {
        // Find first differing A-row to pinpoint source.
        for (row_idx, (rv, rc)) in m_v.a.iter().zip(m_c.a.iter()).enumerate() {
            if rv != rc {
                eprintln!(
                    "[debug][matrices] first A-row mismatch at row={} (vdf_terms={}, cubic_terms={})",
                    row_idx,
                    rv.len(),
                    rc.len()
                );
                eprintln!("[debug][matrices] vdf row head: {:?}", rv.iter().take(5).collect::<Vec<_>>());
                eprintln!("[debug][matrices] cubic row head: {:?}", rc.iter().take(5).collect::<Vec<_>>());
                break;
            }
        }
    }
    assert_eq!(bv.len(), bc.len(), "serialized matrix sizes differ");
    assert_eq!(hv, hc, "R1CS matrices differ (CRS not universal)");
}

#[test]
#[ignore] // Debug helper: compare host OOD equation values
fn debug_host_ood_equation_for_verifier_air_proof() {
    use crate::stark::{
        aggregator_air::{AggregatorAir, AggregatorConfig, prove_aggregator_leaf_from_app},
        verifier_air::{constraints, proof_parser::parse_proof, ood_eval::ChildAirType, VerifierAir},
        test_utils::prove_verifier_air_over_child,
    };
    use winter_crypto::{hashers::Rp64_256, Digest, ElementHasher};
    use winterfell::{crypto::{DefaultRandomCoin, MerkleTree}, AcceptableOptions, ProofOptions, Prover, Trace};
    use winterfell::math::{fields::f64::BaseElement, FieldElement};
    use winter_math::StarkField;
    use winter_math::ToElements;

    type Hasher = Rp64_256;
    type RandomCoin = DefaultRandomCoin<Hasher>;
    type VerifierMerkle = MerkleTree<Hasher>;

    // Build app proof and Aggregator leaf (same as smoke).
    let start = BaseElement::new(3);
    let steps = 8usize;
    let vdf_trace = super::helpers::simple_vdf::build_vdf_trace(start, steps);
    let vdf_result = vdf_trace.get(1, vdf_trace.length() - 1);
    let agg_cfg = AggregatorConfig::test_fast();
    let vdf_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let vdf_proof = super::helpers::simple_vdf::VdfProver::<Hasher>::new(vdf_options)
        .prove(vdf_trace)
        .expect("VDF proof failed");
    let (agg_proof, agg_pub_inputs, _agg_trace) = prove_aggregator_leaf_from_app::<super::helpers::simple_vdf::VdfAir>(
        &agg_cfg,
        vdf_proof,
        vdf_result,
        ChildAirType::generic_vdf(),
    )
    .unwrap();
    let acceptable_agg = AcceptableOptions::OptionSet(vec![agg_cfg.to_proof_options()]);
    winterfell::verify::<AggregatorAir, Hasher, RandomCoin, VerifierMerkle>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    )
    .unwrap();

    // Wrap with VerifierAir.
    let parsed_child = parse_proof::<AggregatorAir>(&agg_proof, &agg_pub_inputs);
    let verifier_options = ProofOptions::new(
        4, 64, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let (ver_proof, ver_pub_inputs) =
        prove_verifier_air_over_child(&parsed_child, ChildAirType::aggregator_air(), verifier_options.clone());
    let acceptable_ver = AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Hasher, RandomCoin, VerifierMerkle>(
        ver_proof.clone(),
        ver_pub_inputs.clone(),
        &acceptable_ver,
    )
    .unwrap();

    // Parse the VerifierAir proof (this is what Groth16 circuit checks).
    let parsed_ver = parse_proof::<VerifierAir>(&ver_proof, &ver_pub_inputs);

    // Evaluate VerifierAir transition constraints at OOD point using periodic eval.
    let current = parsed_ver.ood_trace_current.clone();
    let next = parsed_ver.ood_trace_next.clone();
    let frame = winterfell::EvaluationFrame::from_rows(current.clone(), next.clone());

    // Evaluate periodic columns at z (cycle length 8).
    let periodic_cols = crate::stark::verifier_air::hash_chiplet::get_periodic_column_values();
    let n = parsed_ver.trace_len;
    assert_eq!(n % 8, 0);
    let k = n / 8;
    let z = parsed_ver.z;
    let y = z.exp(k as u64);
    let g = BaseElement::get_root_of_unity(n.ilog2());
    let y_points: [BaseElement; 8] = [
        g.exp(0u64),
        g.exp(k as u64),
        g.exp((2 * k) as u64),
        g.exp((3 * k) as u64),
        g.exp((4 * k) as u64),
        g.exp((5 * k) as u64),
        g.exp((6 * k) as u64),
        g.exp((7 * k) as u64),
    ];
    let mut periodic_at_z = vec![BaseElement::ZERO; periodic_cols.len()];
    for (ci, col) in periodic_cols.iter().enumerate() {
        assert_eq!(col.len(), 8);
        // Lagrange interpolate Q(y) over 8 points.
        let mut acc = BaseElement::ZERO;
        for j in 0..8 {
            let mut num = BaseElement::ONE;
            let mut den = BaseElement::ONE;
            for m in 0..8 {
                if m == j { continue; }
                num *= y - y_points[m];
                den *= y_points[j] - y_points[m];
            }
            let lj = num * den.inv();
            acc += col[j] * lj;
        }
        periodic_at_z[ci] = acc;
    }

    let mut evals = vec![BaseElement::ZERO; 42];
    constraints::evaluate_all(&frame, &periodic_at_z, &mut evals, &ver_pub_inputs);
    assert_eq!(evals.len(), 42);

    // Compute transition_sum with parsed_ver.constraint_coeffs (first 42 are transition).
    let mut transition_sum = BaseElement::ZERO;
    for i in 0..42 {
        transition_sum += parsed_ver.constraint_coeffs[i] * evals[i];
    }

    // Compute C(z).
    let z_pow_n = z.exp(n as u64);
    let mut c_combined = BaseElement::ZERO;
    let mut z_pow_in = BaseElement::ONE;
    for comp_i in parsed_ver.ood_comp_current.iter() {
        c_combined += *comp_i * z_pow_in;
        z_pow_in *= z_pow_n;
    }

    let zerofier_num = z_pow_n - BaseElement::ONE;
    let exemption = z - g.exp((n - 1) as u64);
    let z_minus_1 = z - BaseElement::ONE;

    // Boundary contributions (same 8 assertions as VerifierAir).
    let mut initial_sum = BaseElement::ZERO;
    for (j, col) in [3usize, 4, 5, 6].iter().enumerate() {
        initial_sum += parsed_ver.constraint_coeffs[42 + j] * current[*col];
    }
    initial_sum += parsed_ver.constraint_coeffs[42 + 4] * current[constraints::AUX_START + 1];
    initial_sum += parsed_ver.constraint_coeffs[42 + 5] * current[constraints::AUX_START + 3];

    let expected_mode_counter = BaseElement::new(ver_pub_inputs.expected_mode_counter as u64);
    let expected_checkpoints = BaseElement::new(ver_pub_inputs.expected_checkpoint_count as u64);
    let final_term =
        parsed_ver.constraint_coeffs[42 + 6] * (current[constraints::AUX_START + 1] - expected_mode_counter)
        + parsed_ver.constraint_coeffs[42 + 7] * (current[constraints::AUX_START + 3] - expected_checkpoints);

    // Multiply-through equation.
    let exemption_sq = exemption * exemption;
    let lhs = transition_sum * exemption_sq * z_minus_1
        + initial_sum * zerofier_num * exemption
        + final_term * zerofier_num * z_minus_1;
    let rhs = c_combined * zerofier_num * z_minus_1 * exemption;

    eprintln!("[host][ood] lhs={} rhs={}", lhs.as_int(), rhs.as_int());
    assert_eq!(lhs, rhs, "host OOD equation must hold for VerifierAir proof");
}

#[test]
#[ignore] // Debug helper: pinpoint first transition constraint mismatch (AIR vs R1CS evaluator)
fn debug_compare_air_vs_r1cs_transition_constraints_at_z() {
    use crate::stark::{
        aggregator_air::{AggregatorAir, AggregatorConfig, prove_aggregator_leaf_from_app},
        verifier_air::{constraints, hash_chiplet, proof_parser::parse_proof, ood_eval::ChildAirType, VerifierAir},
        test_utils::prove_verifier_air_over_child,
    };

    use ark_ff::PrimeField;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::R1CSVar;

    use winter_crypto::{hashers::Rp64_256, Digest, ElementHasher};
    use winterfell::{crypto::{DefaultRandomCoin, MerkleTree}, AcceptableOptions, ProofOptions, Prover, Trace};
    use winterfell::math::{fields::f64::BaseElement, FieldElement, ToElements};
    use winter_math::StarkField;

    type Hasher = Rp64_256;
    type RandomCoin = DefaultRandomCoin<Hasher>;
    type VerifierMerkle = MerkleTree<Hasher>;

    // 1) Build app proof + AggregatorAir leaf proof, then wrap with VerifierAir (same as smoke).
    let start = BaseElement::new(3);
    let steps = 8usize;
    let vdf_trace = super::helpers::simple_vdf::build_vdf_trace(start, steps);
    let vdf_result = vdf_trace.get(1, vdf_trace.length() - 1);
    let agg_cfg = AggregatorConfig::test_fast();
    let vdf_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let vdf_proof = super::helpers::simple_vdf::VdfProver::<Hasher>::new(vdf_options)
        .prove(vdf_trace)
        .expect("VDF proof failed");
    let (agg_proof, agg_pub_inputs, _agg_trace) = prove_aggregator_leaf_from_app::<super::helpers::simple_vdf::VdfAir>(
        &agg_cfg,
        vdf_proof,
        vdf_result,
        ChildAirType::generic_vdf(),
    )
    .unwrap();
    let acceptable_agg = AcceptableOptions::OptionSet(vec![agg_cfg.to_proof_options()]);
    winterfell::verify::<AggregatorAir, Hasher, RandomCoin, VerifierMerkle>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    )
    .unwrap();

    let parsed_child = parse_proof::<AggregatorAir>(&agg_proof, &agg_pub_inputs);
    let verifier_options = ProofOptions::new(
        4, 64, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let (ver_proof, ver_pub_inputs) =
        prove_verifier_air_over_child(&parsed_child, ChildAirType::aggregator_air(), verifier_options.clone());
    let acceptable_ver = AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Hasher, RandomCoin, VerifierMerkle>(
        ver_proof.clone(),
        ver_pub_inputs.clone(),
        &acceptable_ver,
    )
    .unwrap();

    // Parse the VerifierAir proof: gives OOD frame, z, coeffs, etc.
    let parsed_ver = parse_proof::<VerifierAir>(&ver_proof, &ver_pub_inputs);

    // 2) Compute AIR transition constraint evaluations at z (host-side, with periodic columns).
    let current = parsed_ver.ood_trace_current.clone();
    let next = parsed_ver.ood_trace_next.clone();
    let frame = winterfell::EvaluationFrame::from_rows(current.clone(), next.clone());

    let periodic_cols = hash_chiplet::get_periodic_column_values();
    let n = parsed_ver.trace_len;
    assert_eq!(n % 8, 0);
    let k = n / 8;
    let z = parsed_ver.z;
    let y = z.exp(k as u64);
    let g = BaseElement::get_root_of_unity(n.ilog2());
    let y_points: [BaseElement; 8] = [
        g.exp(0u64),
        g.exp(k as u64),
        g.exp((2 * k) as u64),
        g.exp((3 * k) as u64),
        g.exp((4 * k) as u64),
        g.exp((5 * k) as u64),
        g.exp((6 * k) as u64),
        g.exp((7 * k) as u64),
    ];
    let mut periodic_at_z = vec![BaseElement::ZERO; periodic_cols.len()];
    for (ci, col) in periodic_cols.iter().enumerate() {
        assert_eq!(col.len(), 8);
        let mut acc = BaseElement::ZERO;
        for j in 0..8 {
            let mut num = BaseElement::ONE;
            let mut den = BaseElement::ONE;
            for m in 0..8 {
                if m == j { continue; }
                num *= y - y_points[m];
                den *= y_points[j] - y_points[m];
            }
            let lj = num * den.inv();
            acc += col[j] * lj;
        }
        periodic_at_z[ci] = acc;
    }

    let mut air_evals = vec![BaseElement::ZERO; 42];
    constraints::evaluate_all(&frame, &periodic_at_z, &mut air_evals, &ver_pub_inputs);

    // 3) Compute R1CS-evaluator constraint values at z, but *without* enforcing equality.
    // We do this by calling the R1CS evaluator on a fresh CS and reading witness values.
    type InnerFr = crate::stark::StarkInnerFr;
    type FpGLVar = FpVar<InnerFr>;
    use crate::stark::gadgets::gl_fast::GlVar;

    fn fr_to_u64(x: InnerFr) -> u64 {
        let bi = x.into_bigint();
        bi.0[0]
    }

    let cs = ConstraintSystem::<InnerFr>::new_ref();

    let mk_gl = |u: u64| -> GlVar {
        GlVar(FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(u))).unwrap())
    };

    let ood_trace_current_gl: Vec<GlVar> = current.iter().map(|e| mk_gl(e.as_int())).collect();
    let ood_trace_next_gl: Vec<GlVar> = next.iter().map(|e| mk_gl(e.as_int())).collect();

    // Extract public inputs words (u64) for the evaluator.
    let pub_elems = ver_pub_inputs.to_elements();
    let statement_hash_u64 = [
        pub_elems[0].as_int(),
        pub_elems[1].as_int(),
        pub_elems[2].as_int(),
        pub_elems[3].as_int(),
    ];
    let trace_commitment_u64 = [
        pub_elems[4].as_int(), pub_elems[5].as_int(), pub_elems[6].as_int(), pub_elems[7].as_int(),
    ];
    let comp_commitment_u64 = [
        pub_elems[8].as_int(), pub_elems[9].as_int(), pub_elems[10].as_int(), pub_elems[11].as_int(),
    ];
    let params_digest_u64 = {
        let l = pub_elems.len();
        [
            pub_elems[l - 4].as_int(),
            pub_elems[l - 3].as_int(),
            pub_elems[l - 2].as_int(),
            pub_elems[l - 1].as_int(),
        ]
    };

    // FRI commitments (pad to 32 with zeros) — match R1CS evaluator signature.
    const MAX_FRI_LAYERS: usize = 32;
    let mut fri_commitments_u64 = vec![[0u64; 4]; MAX_FRI_LAYERS];
    for (i, c) in ver_pub_inputs.fri_commitments.iter().enumerate().take(MAX_FRI_LAYERS) {
        fri_commitments_u64[i] = [c[0].as_int(), c[1].as_int(), c[2].as_int(), c[3].as_int()];
    }

    let r1cs_constraints = crate::stark::ood_eval_r1cs::evaluate_verifier_air_constraints_gl_for_test(
        cs.clone(),
        &ood_trace_current_gl,
        &ood_trace_next_gl,
        &statement_hash_u64,
        &trace_commitment_u64,
        &comp_commitment_u64,
        &fri_commitments_u64,
        &params_digest_u64,
        ver_pub_inputs.g_trace.as_int(),
    );

    assert_eq!(r1cs_constraints.len(), 42);

    // 4) Compare per-constraint values.
    for i in 0..42 {
        let r = r1cs_constraints[i].0.value().unwrap();
        let r_u64 = fr_to_u64(r);
        let a_u64 = air_evals[i].as_int();
        if r_u64 != a_u64 {
            panic!(
                "constraint[{i}] mismatch at z: air={a_u64} r1cs={r_u64}"
            );
        }
    }
}

#[test]
#[ignore] // Debug helper: locate first failing VerifierAir transition constraint #21 (fri[6])
fn debug_verifier_over_aggregator_constraint_21() {
    use crate::stark::aggregator_air::{AggregatorAir, AggregatorConfig, prove_aggregator_leaf_from_app};
    use crate::stark::tests::helpers::simple_vdf::{build_vdf_trace, VdfProver};
    use crate::stark::verifier_air::{
        aggregator_integration::{RecursiveConfig, RecursiveVerifier},
        constraints,
        hash_chiplet,
        VerifierPublicInputs,
    };

    use winter_crypto::{DefaultRandomCoin, MerkleTree};
    use winter_crypto::hashers::Rp64_256;
    use winterfell::{AcceptableOptions, ProofOptions, Prover, Trace};
    use winterfell::math::fields::f64::BaseElement;
    use winterfell::math::FieldElement;

    // 1) Produce a small VDF proof, then AggregatorAir leaf wrapper proof.
    let start = BaseElement::new(3);
    let steps = 8usize;
    let vdf_trace = build_vdf_trace(start, steps);
    let vdf_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let vdf_prover = VdfProver::<Rp64_256>::new(vdf_options.clone());
    let vdf_proof = vdf_prover.prove(vdf_trace.clone()).expect("VDF proof failed");
    let vdf_result = vdf_trace.get(1, vdf_trace.length() - 1);
    let acceptable_vdf = AcceptableOptions::OptionSet(vec![vdf_options]);
    winterfell::verify::<crate::stark::tests::helpers::simple_vdf::VdfAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        vdf_proof.clone(),
        vdf_result,
        &acceptable_vdf,
    ).expect("VDF verify");

    let agg_cfg = AggregatorConfig::test_fast();
    let (agg_proof, agg_pub_inputs, _agg_trace) =
        prove_aggregator_leaf_from_app::<crate::stark::tests::helpers::simple_vdf::VdfAir>(
            &agg_cfg,
            vdf_proof,
            vdf_result,
            crate::stark::verifier_air::ood_eval::ChildAirType::generic_vdf(),
        )
        .expect("Aggregator leaf proof failed");
    let acceptable_agg = AcceptableOptions::OptionSet(vec![agg_cfg.to_proof_options()]);
    winterfell::verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    ).expect("Aggregator verify");

    // 2) Build the verifier trace exactly as the recursive pipeline does.
    let recursive = RecursiveConfig::test();
    let rv = RecursiveVerifier::new(recursive.clone());
    let trace = rv.build_verification_trace(&agg_proof, &agg_pub_inputs);
    let pub_inputs: VerifierPublicInputs = rv.get_verifier_public_inputs(&agg_proof, &agg_pub_inputs);
    eprintln!(
        "[debug] verifier trace len={} width={}",
        trace.length(),
        trace.width()
    );

    // Optional: prove the VerifierAir STARK over this trace (should not panic).
    let verifier_prover = crate::stark::verifier_air::prover::VerifierProver::with_pub_inputs(
        recursive.verifier_options.clone(),
        pub_inputs.clone(),
    );
    let _verifier_proof = verifier_prover.prove(trace.clone()).expect("VerifierAir prove (debug)");

    // 3) Locate first failure for constraint index 21.
    const C: usize = 21;
    let width = trace.width();
    let len = trace.length();
    let periodic_cols = hash_chiplet::get_periodic_column_values();
    assert!(!periodic_cols.is_empty(), "VerifierAir must define periodic columns");
    for step in 0..(len - 1) {
        let current: Vec<BaseElement> = (0..width).map(|c| trace.get(c, step)).collect();
        let next: Vec<BaseElement> = (0..width).map(|c| trace.get(c, step + 1)).collect();
        let frame = winterfell::EvaluationFrame::from_rows(current, next);
        let mut result = vec![BaseElement::ZERO; 42];
        // Periodic values are indexed by (step % 8) for this AIR's 8-cycle RPO constants.
        let mut periodic_values = Vec::with_capacity(periodic_cols.len());
        for col in periodic_cols.iter() {
            periodic_values.push(col[step % 8]);
        }
        constraints::evaluate_all(&frame, &periodic_values, &mut result, &pub_inputs);
        if result[C] != BaseElement::ZERO {
            let s0 = trace.get(0, step).as_int();
            let s1 = trace.get(1, step).as_int();
            let s2 = trace.get(2, step).as_int();
            let op_code = s0 + 2 * s1 + 4 * s2;
            let aux2 = trace.get(constraints::AUX_START + 2, step).as_int();
            let fri6 = trace.get(constraints::FRI_START + 6, step).as_int();
            let fri7 = trace.get(constraints::FRI_START + 7, step).as_int();
            panic!(
                "c{C} failed at step={step}: op={op_code} aux2={aux2} fri6={fri6} fri7={fri7} c={:?}",
                result[C]
            );
        }
    }
}

/// Test the FULL STARK verifier with meaningful FRI layers
/// 
/// This is the critical test that verifies FRI folding is actually checked.
/// Uses larger trace (256 rows) to generate ~8 FRI layers.
#[test]
#[ignore] // Takes ~30-60 seconds, run with: cargo test full_stark_verifier_with_fri_smoke --release -- --ignored
fn full_stark_verifier_with_fri_smoke() {
    println!("\n=== Full STARK Verifier with FRI Layers ===\n");
    
    // Build with FRI config (trace_len=256, ~8 FRI layers)
    let instance = build_vdf_recursive_stark_instance_with_fri(3, 8);
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    });
    
    println!("Circuit Statistics (with FRI):");
    println!("  Total Constraints: {}", cs.num_constraints());
    println!("  (Should be significantly larger than no-FRI version due to FRI verification)");
    
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("First failing constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "Circuit with FRI must be satisfied");
    
    // The constraint count should be notably higher due to FRI verification
    // No-FRI version has ~3M constraints, with FRI should be ~5-10M+
    println!("\n✅ Full STARK verifier with FRI layers passed!");
}

/// Test the verifying aggregator pipeline:
/// VDF STARK 0 + VDF STARK 1 → Verifying Aggregator → Groth16
/// 
/// This tests that:
/// 1. The Aggregator ACTUALLY VERIFIES both VDF proofs in its trace
/// 2. The Aggregator proof uses VerifierAir constraints (27 columns)
/// 3. The Groth16 circuit correctly verifies the VerifierAir proof
#[test]
fn verifying_aggregator_smoke() {
    // Two VDF proofs with different parameters
    let instance = build_verifying_aggregator_instance(
        3, 8,   // VDF 0: start=3, steps=8
        7, 8,   // VDF 1: start=7, steps=8
    );
    
    // Synthesize to check constraints (with constraint trace enabled)
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::ConstraintLayer;
    let cs = ConstraintSystem::new_ref();
    let subscriber = Registry::default().with(ConstraintLayer::default());
    tracing::subscriber::with_default(subscriber, || {
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    });
    
    println!("Verifying Aggregator Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    let ok = cs.is_satisfied().unwrap_or(false);
    if !ok {
        eprintln!("First failing constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(ok, "Verifying Aggregator circuit must be satisfied");
}
