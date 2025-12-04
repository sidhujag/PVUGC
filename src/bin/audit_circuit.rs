//! PVUGC Trapdoor-Aware Audit Tool
//!
//! This tool audits circuits for algebraic security.
//! It performs:
//! 1. **Linearity Check**: Verifies that Public Inputs do not multiply each other.
//! 2. **Independence Check**: Verifies that the "Baked Quotient" Target lies outside the linear span of the
//!    "Lean CRS" + "Ciphertext" handles in the Generic Bilinear Group Model (AGBGM).
//!
//! Optimization: Uses streaming column processing + Incremental Basis + Sparse Eval.

use ark_ff::{Field, One, Zero};
use ark_groth16::Groth16;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination, Variable,
};
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use arkworks_groth16::{
    outer_compressed::{DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterFr},
    test_circuits::AddCircuit,
    test_fixtures::get_fixture,
};
use std::collections::{HashMap, HashSet};

type Fr = OuterFr;

// All handles/targets are multiplied by delta to clear denominators from L-queries.
// Base ring: F[alpha, beta, gamma, delta, x]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TrapdoorMonomial {
    // --- Target Terms (scaled by delta) ---
    AlphaBetaDelta, // alpha * beta * delta
    // GammaDelta removed because gamma cancels out in e(L, gamma).
    // Instead, we model the expanded terms of L*delta directly.
    DeltaSq, // Any(x) * delta^2 (Merges H and u terms)

    // --- Handle Terms from L_k * D_pub (1/delta * delta cancels) ---
    // Result is (beta*u + alpha*v + w)(beta + V)
    BetaSqU,    // beta^2 * u
    BetaU,      // beta * u * V
    AlphaBetaV, // alpha * beta * v
    AlphaV,     // alpha * v * V
    BetaW,      // beta * w
    W,          // w * V

    // Result is (beta*u + ...)(v_j)
    BetaUV,  // beta * u * v
    AlphaVV, // alpha * v * v
    WV,      // w * v

    // --- Handle Terms from L_k * D_delta (Clean L * delta) ---
    // Result is (beta*u + alpha*v + w) * delta
    BetaDeltaU,  // beta * delta * u
    AlphaDeltaV, // alpha * delta * v
    DeltaW,      // delta * w

    // --- Handle Terms from u_k * D_pub (Clean u * delta) ---
    // u * (beta + V) * delta = beta*delta*u + delta*u*V
    // BetaDeltaU is already defined above (MATCH!)
    DeltaUV, // delta * u * V

    // --- Handle Terms from u_k * D_delta (Clean u * delta) ---
    // u * delta * delta = delta^2 * u
    // Merged into DeltaSq

    // --- Handle Terms from u_k * D_j (Clean u * v * delta) ---
    // u * v * delta
    DeltaPureUV, // delta * u * v

    // --- Fixed Alpha Handles ---
    // alpha * D_pub * delta = alpha(beta+V)delta = alpha*beta*delta + alpha*V*delta
    // AlphaDeltaV represents alpha * delta * V_pub

    // alpha * D_delta * delta = alpha * delta^2
    AlphaDeltaSq, // alpha * delta^2

    // --- Raw B-Query Handles (from b_g1_query and b_g2_query) ---
    // These are available for ALL variables in standard Groth16.
    // v_k (G1) * beta (G2) -> v * beta
    BetaV,
    // v_k (G1) * v_j (G2) -> v * v
    PureVV,
    // --- Static GT table handles (deg_rho = 0) ---
    AlphaBetaStatic,  // alpha * beta
    AlphaDeltaStatic, // alpha * delta
    AlphaVStatic,     // alpha * v
}

struct TrapdoorPolyVector {
    components: Vec<(TrapdoorMonomial, DensePolynomial<Fr>)>,
}

impl TrapdoorPolyVector {
    fn new(components: Vec<(TrapdoorMonomial, DensePolynomial<Fr>)>) -> Self {
        Self { components }
    }
}

// --- Audit Subjects ---

trait AuditSubject {
    fn name(&self) -> &'static str;
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()>;
}

struct ProductionSubject(OuterCircuit<DefaultCycle>);
impl AuditSubject for ProductionSubject {
    fn name(&self) -> &'static str {
        "Production OuterCircuit"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        self.0.clone().generate_constraints(cs)
    }
}

struct MockLinear;
impl AuditSubject for MockLinear {
    fn name(&self) -> &'static str {
        "Mock Linear (Safe)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        // Public input is a hash h = w1 + w2 (fixed here to 5)
        let hash_val = Fr::from(5u64);
        let mut one_lc = LinearCombination::zero();
        one_lc += (Fr::one(), Variable::One);

        let h_pub = cs.new_input_variable(|| Ok(hash_val))?;

        // Witness values for the underlying statement
        let w1 = cs.new_witness_variable(|| Ok(Fr::from(2u64)))?;
        let w2 = cs.new_witness_variable(|| Ok(Fr::from(3u64)))?;

        // Witness copy of the hash
        let h_wit = cs.new_witness_variable(|| Ok(hash_val))?;

        // Witness-only relation: w1 + w2 = h_wit
        let mut lc_b = LinearCombination::zero();
        lc_b += (Fr::one(), w1);
        lc_b += (Fr::one(), w2);
        let mut lc_c = LinearCombination::zero();
        lc_c += (Fr::one(), h_wit);
        cs.enforce_constraint(one_lc.clone(), lc_b, lc_c)?;

        // Public binding: 1 * h_pub = h_wit
        let mut lc_b2 = LinearCombination::zero();
        lc_b2 += (Fr::one(), h_pub);
        let mut lc_c2 = LinearCombination::zero();
        lc_c2 += (Fr::one(), h_wit);
        cs.enforce_constraint(one_lc, lc_b2, lc_c2)?;
        Ok(())
    }
}

struct MockQuadratic;
impl AuditSubject for MockQuadratic {
    fn name(&self) -> &'static str {
        "Mock Quadratic (Unsafe)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        use ark_r1cs_std::prelude::*;
        let x = ark_r1cs_std::fields::fp::FpVar::new_input(cs.clone(), || Ok(Fr::one()))?;
        let one = ark_r1cs_std::fields::fp::FpVar::constant(Fr::from(1));
        x.mul_equals(&x, &one)?;
        Ok(())
    }
}

fn main() {
    println!("PVUGC Production Audit Tool");
    println!("===========================\n");

    let subjects: Vec<Box<dyn AuditSubject>> = vec![
        Box::new(MockLinear),
        Box::new(MockQuadratic),
        Box::new(ProductionSubject(get_valid_circuit())),
    ];

    for subject in subjects {
        println!(">>> AUDITING: {} <<<", subject.name());
        run_audit(subject.as_ref());
        println!("\n");
    }
}

fn run_audit(subject: &dyn AuditSubject) {
    let cs = ConstraintSystem::<Fr>::new_ref();
    subject.synthesize(cs.clone()).unwrap();
    cs.finalize();
    println!("Constraints: {}", cs.num_constraints());
    let num_pub = cs.num_instance_variables();
    let num_wit = cs.num_witness_variables();
    println!("Public: {}, Witness: {}", num_pub, num_wit);

    let extractor = MatrixExtractor::new(cs.clone());

    // 0. Check public column structure (Lean CRS diagnostic)
    let mut public_inputs_a_zero = true; // Columns 1..num_pub (actual public inputs)
    let mut public_inputs_b_nonzero = true; // Columns 1..num_pub MUST be in B
    let constant_one_has_a = !extractor.a_cols[0].is_empty(); // Column 0 (constant "1")

    for i in 1..num_pub {
        // Skip column 0 (constant "1" is expected to have A entries)
        let a_count = extractor.a_cols[i].len();
        let b_count = extractor.b_cols[i].len();
        let c_count = extractor.c_cols[i].len();

        println!(
            "  [Column {}] A={}, B={}, C={}",
            i, a_count, b_count, c_count
        );

        if a_count > 0 {
            public_inputs_a_zero = false;
            println!(
                "  [FAIL] Column {} has A entries! Public inputs must be A-free.",
                i
            );
        }

        if b_count == 0 {
            public_inputs_b_nonzero = false;
            println!(
                "  [FAIL] Column {} has B=0! Public inputs must be in B for statement dependency.",
                i
            );
        }

        // Check if IC_i would be zero (security issue!)
        if b_count == 0 && c_count == 0 {
            println!(
                "  [SECURITY] Column {} has v_i=0 AND w_i=0 → IC_i=0 → PUBLIC INPUT NOT VERIFIED!",
                i
            );
        }
    }

    if constant_one_has_a {
        println!(
            "  [Column 0] Constant '1' has {} A entries (expected, baked into α)",
            extractor.a_cols[0].len()
        );
    }

    if public_inputs_a_zero && public_inputs_b_nonzero {
        println!("[PASS] Public input structure valid (A=0, B>0) → Lean CRS compatible & Statement Dependent");
    } else {
        println!("[FAIL] Public input structure INVALID (Check A=0 and B>0 requirements)");
    }

    // Additional guard: ensure no public column appears in both A and B on the same row
    let no_pub_ab_overlap = check_public_ab_overlap(&extractor, num_pub);
    if no_pub_ab_overlap {
        println!("[PASS] Public columns never share A/B rows.");
    } else {
        println!("[FAIL] Public column appears in both A and B on same row.");
    }

    // 1. Linearity Check
    let mut pub_polys = Vec::new();
    for i in 0..num_pub {
        pub_polys.push(extractor.get_column_polys(i));
    }

    let is_linear = check_linearity(&pub_polys, num_pub);
    if is_linear {
        println!("[PASS] Linearity Check.");
    } else {
        println!("[FAIL] Linearity Check (Public*Public detected).");
    }

    // 1.5 Mixing Check (Public * Witness)
    let is_unmixed = check_mixing(&extractor, num_pub, num_pub + num_wit);
    if is_unmixed {
        println!("[PASS] Mixing Check.");
    } else {
        println!("[FAIL] Mixing Check (Public*Witness detected).");
    }

    // 2. Independence Check
    let h_const = compute_h_const(&pub_polys, &extractor.domain);
    let target = build_target(&pub_polys, &h_const);

    let num_checks = 1;
    let all_safe = run_independence_checks(
        "",
        &extractor,
        &pub_polys,
        &target,
        num_pub + num_wit,
        num_checks,
    );

    println!(
        "RESULT: {}",
        if is_linear && is_unmixed && all_safe && no_pub_ab_overlap {
            "SAFE"
        } else {
            "UNSAFE"
        }
    );
}

fn check_public_ab_overlap(extractor: &MatrixExtractor, num_pub: usize) -> bool {
    for col in 1..num_pub {
        if extractor.a_cols[col].is_empty() || extractor.b_cols[col].is_empty() {
            continue;
        }
        let rows_b: HashSet<usize> = extractor.b_cols[col].iter().map(|(row, _)| *row).collect();
        for (row, _) in &extractor.a_cols[col] {
            if rows_b.contains(row) {
                println!(
                    "  [FAIL] Column {} appears in both A and B on row {}",
                    col, row
                );
                return false;
            }
        }
    }
    true
}

fn check_mixing(extractor: &MatrixExtractor, num_pub: usize, num_vars: usize) -> bool {
    let domain_size = extractor.domain.size();
    let mut rows_pub_a = vec![false; domain_size];
    let mut rows_pub_b = vec![false; domain_size];

    // Mark rows where Public Inputs (excluding 1) appear in A and B
    for i in 1..num_pub {
        for &(row, _) in &extractor.a_cols[i] {
            rows_pub_a[row] = true;
        }
        for &(row, _) in &extractor.b_cols[i] {
            rows_pub_b[row] = true;
        }
    }

    // Check Witness columns
    for j in num_pub..num_vars {
        // If Witness in A, check if Row has Public in B
        for &(row, _) in &extractor.a_cols[j] {
            if rows_pub_b[row] {
                return false;
            }
        }
        // If Witness in B, check if Row has Public in A
        for &(row, _) in &extractor.b_cols[j] {
            if rows_pub_a[row] {
                return false;
            }
        }
    }
    true
}

fn get_valid_circuit() -> OuterCircuit<DefaultCycle> {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let fixture = get_fixture();
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let circuit_inner = AddCircuit::with_public_input(x_val);
    let proof_inner =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).expect("inner proof");

    let x_inner = vec![x_val];

    OuterCircuit::new((*fixture.vk_inner).clone(), x_inner, proof_inner)
}

struct MatrixExtractor {
    a_cols: Vec<Vec<(usize, Fr)>>,
    b_cols: Vec<Vec<(usize, Fr)>>,
    c_cols: Vec<Vec<(usize, Fr)>>,
    domain: GeneralEvaluationDomain<Fr>,
}

impl MatrixExtractor {
    fn new(cs: ConstraintSystemRef<Fr>) -> Self {
        let matrices = cs.to_matrices().expect("matrix extraction");
        let domain_size = cs.num_constraints().next_power_of_two();
        let domain = GeneralEvaluationDomain::<Fr>::new(domain_size).expect("domain");

        let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
        let mut a_cols = vec![Vec::new(); num_vars];
        let mut b_cols = vec![Vec::new(); num_vars];
        let mut c_cols = vec![Vec::new(); num_vars];

        for (row, terms) in matrices.a.iter().enumerate() {
            if row < domain_size {
                for &(val, col) in terms {
                    a_cols[col].push((row, val));
                }
            }
        }
        for (row, terms) in matrices.b.iter().enumerate() {
            if row < domain_size {
                for &(val, col) in terms {
                    b_cols[col].push((row, val));
                }
            }
        }
        for (row, terms) in matrices.c.iter().enumerate() {
            if row < domain_size {
                for &(val, col) in terms {
                    c_cols[col].push((row, val));
                }
            }
        }

        Self {
            a_cols,
            b_cols,
            c_cols,
            domain,
        }
    }

    fn get_column_polys(
        &self,
        col: usize,
    ) -> (
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    ) {
        let mut u_evals = vec![Fr::zero(); self.domain.size()];
        let mut v_evals = vec![Fr::zero(); self.domain.size()];
        let mut w_evals = vec![Fr::zero(); self.domain.size()];

        for &(row, val) in &self.a_cols[col] {
            u_evals[row] = val;
        }
        for &(row, val) in &self.b_cols[col] {
            v_evals[row] = val;
        }
        for &(row, val) in &self.c_cols[col] {
            w_evals[row] = val;
        }

        (
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&u_evals)),
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&v_evals)),
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&w_evals)),
        )
    }

    fn evaluate_column(&self, col: usize, r: Fr) -> (Fr, Fr, Fr) {
        let n_as_field = self.domain.size_as_field_element();
        let n_inv = n_as_field.inverse().unwrap();
        let z_h_at_r = r.pow([self.domain.size() as u64]) - Fr::one();
        let common = z_h_at_r * n_inv;

        let eval_sparse = |sparse: &Vec<(usize, Fr)>| -> Fr {
            let mut acc = Fr::zero();
            for &(row, val) in sparse {
                let omega_i = self.domain.element(row);
                let denom = r - omega_i;
                acc += (val * omega_i) * denom.inverse().unwrap();
            }
            acc * common
        };

        (
            eval_sparse(&self.a_cols[col]),
            eval_sparse(&self.b_cols[col]),
            eval_sparse(&self.c_cols[col]),
        )
    }
}

fn check_linearity(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    num_pub: usize,
) -> bool {
    for i in 1..num_pub {
        for j in 1..num_pub {
            let prod = &pub_polys[i].0 * &pub_polys[j].1;
            if !prod.is_zero() {
                return false;
            }
        }
    }
    true
}

fn compute_h_const(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    domain: &GeneralEvaluationDomain<Fr>,
) -> DensePolynomial<Fr> {
    let mut a_pub = DensePolynomial::zero();
    let mut b_pub = DensePolynomial::zero();
    let mut c_pub = DensePolynomial::zero();
    for (u, v, w) in pub_polys {
        a_pub += u;
        b_pub += v;
        c_pub += w;
    }
    let numerator = &(&a_pub * &b_pub) - &c_pub;
    let (h, _) = numerator.divide_by_vanishing_poly(*domain);
    h
}

fn build_target(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    h_const: &DensePolynomial<Fr>,
) -> TrapdoorPolyVector {
    // Reconstruct L_pub components
    // L_pub = Sum x_i (beta u_i + alpha v_i + w_i)
    // Normalized Target (x delta) = alpha*beta*delta + delta * L_pub - H*delta^2
    // = alpha*beta*delta + beta*delta*U + alpha*delta*V + delta*W - H*delta^2

    let mut u_sum = DensePolynomial::zero();
    let mut v_sum = DensePolynomial::zero();
    let mut w_sum = DensePolynomial::zero();

    for (u, v, w) in pub_polys {
        u_sum += u;
        v_sum += v;
        w_sum += w;
    }

    TrapdoorPolyVector::new(vec![
        (
            TrapdoorMonomial::AlphaBetaDelta,
            DensePolynomial::from_coefficients_slice(&[Fr::one()]),
        ),
        (TrapdoorMonomial::BetaDeltaU, u_sum),
        (TrapdoorMonomial::AlphaDeltaV, v_sum),
        (TrapdoorMonomial::DeltaW, w_sum),
        (TrapdoorMonomial::DeltaSq, -h_const.clone()),
    ])
}

struct Basis {
    rows: Vec<Vec<Fr>>,
    pivots: Vec<usize>,
}

impl Basis {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            pivots: Vec::new(),
        }
    }

    fn reduce(&self, mut v: Vec<Fr>) -> Vec<Fr> {
        for (i, row) in self.rows.iter().enumerate() {
            let p = self.pivots[i];
            if !v[p].is_zero() {
                let factor = v[p];
                for k in p..v.len() {
                    v[k] -= factor * row[k];
                }
            }
        }
        v
    }

    fn insert(&mut self, v: Vec<Fr>) {
        let reduced = self.reduce(v);
        if let Some(p) = reduced.iter().position(|x| !x.is_zero()) {
            let inv = reduced[p].inverse().unwrap();
            let normalized: Vec<Fr> = reduced.iter().map(|x| *x * inv).collect();
            self.rows.push(normalized);
            self.pivots.push(p);
        }
    }
}

fn check_independence_streaming(
    extractor: &MatrixExtractor,
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    target: &TrapdoorPolyVector,
    num_vars: usize,
    seed: u64,
    check_idx: usize,
    total_checks: usize,
) -> (bool, Option<String>) {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let r = Fr::rand(&mut rng);

    let mut mono_set = std::collections::HashSet::new();
    for (m, _) in &target.components {
        mono_set.insert(m.clone());
    }
    let all_monos = vec![
        TrapdoorMonomial::AlphaBetaDelta,
        TrapdoorMonomial::DeltaSq,
        TrapdoorMonomial::BetaSqU,
        TrapdoorMonomial::BetaU,
        TrapdoorMonomial::AlphaBetaV,
        TrapdoorMonomial::AlphaV,
        TrapdoorMonomial::BetaW,
        TrapdoorMonomial::W,
        TrapdoorMonomial::BetaUV,
        TrapdoorMonomial::AlphaVV,
        TrapdoorMonomial::WV,
        TrapdoorMonomial::BetaDeltaU,
        TrapdoorMonomial::AlphaDeltaV,
        TrapdoorMonomial::DeltaW,
        TrapdoorMonomial::DeltaUV,
        TrapdoorMonomial::DeltaPureUV,
        TrapdoorMonomial::AlphaDeltaSq,
        TrapdoorMonomial::BetaV,
        TrapdoorMonomial::PureVV,
        TrapdoorMonomial::AlphaBetaStatic,
        TrapdoorMonomial::AlphaDeltaStatic,
        TrapdoorMonomial::AlphaVStatic,
    ];
    for m in all_monos {
        mono_set.insert(m);
    }

    let mut monomials: Vec<_> = mono_set.into_iter().collect();
    monomials.sort();
    let mono_map: HashMap<_, _> = monomials
        .iter()
        .enumerate()
        .map(|(i, m)| (m.clone(), i))
        .collect();
    let num_dims = monomials.len();

    let mut target_vec = vec![Fr::zero(); num_dims];
    for (m, p) in &target.components {
        if let Some(&idx) = mono_map.get(&m) {
            target_vec[idx] = p.evaluate(&r);
        }
    }

    let mut basis = Basis::new();
    let mut dependency_report: Option<String> = None;

    let mut add_basis_vec = |label: &str, col_idx: usize, vec_map: Vec<(TrapdoorMonomial, Fr)>| {
        let mut v = vec![Fr::zero(); num_dims];
        for (m, val) in vec_map {
            if let Some(&idx) = mono_map.get(&m) {
                v[idx] += val;
            }
        }
        basis.insert(v);
        if dependency_report.is_none() {
            let residue = basis.reduce(target_vec.clone());
            if residue.iter().all(|x| x.is_zero()) {
                dependency_report = Some(format!("column {} via {}", col_idx, label));
            }
        }
    };

    let mut v_pub_r = Fr::zero();
    for (_, v, _) in pub_polys {
        v_pub_r += v.evaluate(&r);
    }

    let total_cols = num_vars;
    let step = std::cmp::max(1, total_cols / 20);

    // The adversary has handles for Public Inputs (CRS) AND Witness Inputs (Arming).
    // Skipping 0..num_pub would be UNDER-POWERING the adversary (ignoring public handles).
    let num_pub = pub_polys.len();

    for k in 0..num_vars {
        if k % step == 0 {
            let pct = (k * 100) / total_cols;
            print!(
                "\r[Independence Check {}/{}] Progress: {:3}%",
                check_idx, total_checks, pct
            );
            use std::io::Write;
            let _ = std::io::stdout().flush();
        }

        let (u_val, v_val, w_val) = extractor.evaluate_column(k, r);

        // 1. u_k * D_pub * delta -> beta*delta*u + delta*u*V
        add_basis_vec(
            "u_k * D_pub * delta",
            k,
            vec![
                (TrapdoorMonomial::BetaDeltaU, u_val),
                (TrapdoorMonomial::DeltaUV, u_val * v_pub_r),
            ],
        );

        // 2. u_k * D_delta * delta -> u * delta^2
        add_basis_vec(
            "u_k * D_delta * delta",
            k,
            vec![(TrapdoorMonomial::DeltaSq, u_val)],
        );

        // 3. u_k * D_j * delta -> u * v_j * delta
        add_basis_vec(
            "u_k * D_j * delta",
            k,
            vec![(TrapdoorMonomial::DeltaPureUV, u_val)],
        );

        if k >= num_pub {
            // 4. L_k * D_pub * delta -> (beta*u+alpha*v+w)(beta+V)
            add_basis_vec(
                "L_k * D_pub * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaSqU, u_val),
                    (TrapdoorMonomial::BetaU, u_val * v_pub_r),
                    (TrapdoorMonomial::AlphaBetaV, v_val),
                    (TrapdoorMonomial::AlphaV, v_val * v_pub_r),
                    (TrapdoorMonomial::BetaW, w_val),
                    (TrapdoorMonomial::W, w_val * v_pub_r),
                ],
            );

            // 5. L_k * D_delta * delta -> (beta*u+alpha*v+w) * delta
            // = beta*delta*u + alpha*delta*v + delta*w
            add_basis_vec(
                "L_k * D_delta * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaDeltaU, u_val),
                    (TrapdoorMonomial::AlphaDeltaV, v_val),
                    (TrapdoorMonomial::DeltaW, w_val),
                ],
            );

            // 6. L_k * D_j * delta -> (beta*u+alpha*v+w) * v_j
            // Model as (beta*u + alpha*v + w) * Any
            // = BetaUV * u + AlphaVV * v + WV * w
            add_basis_vec(
                "L_k * D_j * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaUV, u_val),
                    (TrapdoorMonomial::AlphaVV, v_val),
                    (TrapdoorMonomial::WV, w_val),
                ],
            );
        }

        // 7. Raw B-Query Handles (b_g1_query)
        // Available for ALL variables (including public).
        // v_k (G1) * delta (G2) -> v * delta.
        add_basis_vec("Raw B DeltaSq", k, vec![(TrapdoorMonomial::DeltaSq, v_val)]);
        // v_k (G1) * beta (G2) -> v * beta
        add_basis_vec("Raw B BetaV", k, vec![(TrapdoorMonomial::BetaV, v_val)]);
        add_basis_vec("Raw B PureVV", k, vec![(TrapdoorMonomial::PureVV, v_val)]);
    }
    println!(
        "\r[Independence Check {}/{}] Progress: 100%",
        check_idx, total_checks
    );

    // 8. Static GT table handles (deg_rho = 0).
    // T_beta = e(alpha, beta)  → AlphaBetaStatic
    add_basis_vec(
        "GT T_beta (alpha*beta, no delta)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaBetaStatic, Fr::one())],
    );

    // T_delta = e(alpha, delta) → AlphaDeltaStatic
    add_basis_vec(
        "GT T_delta (alpha*delta, no delta^2)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaStatic, Fr::one())],
    );

    // T_v[i] = e(alpha, B_i) for *all* B-columns.
    // The adversary gets the span of {alpha * v_i}; we model that as one generic AlphaVStatic direction.
    // You can refine this later if you want multiple independent directions.
    add_basis_vec(
        "GT T_v aggregate (alpha*v, no delta)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaVStatic, Fr::one())],
    );

    let residue = basis.reduce(target_vec);
    let is_safe = residue.iter().all(|x| x.is_zero()) == false;
    (is_safe, dependency_report)
}

fn run_independence_checks(
    label: &str,
    extractor: &MatrixExtractor,
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    target: &TrapdoorPolyVector,
    num_vars: usize,
    num_checks: usize,
) -> bool {
    let mut all_safe = true;
    println!(
        "[Independence Check{}] Running {} iterations for robustness...",
        label, num_checks
    );
    for i in 0..num_checks {
        let seed = 12345 + i as u64;
        let (is_safe, dependency) = check_independence_streaming(
            extractor,
            pub_polys,
            target,
            num_vars,
            seed,
            i + 1,
            num_checks,
        );
        if !is_safe {
            all_safe = false;
            println!(
                "[FAIL] Independence Check{} iteration {} found dependency!",
                label,
                i + 1
            );
            if let Some(info) = dependency {
                println!("        Dependency witness: {}", info);
            }
            break;
        }
    }
    if all_safe {
        println!(
            "[PASS] Independence Check{} (All {} iterations passed).",
            label, num_checks
        );
    } else {
        println!("[FAIL] Independence Check{} (Target in Span).", label);
    }
    all_safe
}
