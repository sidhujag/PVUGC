//! PVUGC Trapdoor-Aware Audit Tool
//!
//! This tool audits circuits for algebraic security in the AGBGM (Algebraic Generic
//! Bilinear Group Model) for the PVUGC Witness Encryption scheme.
//!
//! ## Security Model
//!
//! With **Full Span Separation** (U, V, W all separated), the minimal secure architecture is:
//!
//! **REQUIRED:**
//! 1. Lean CRS (Baked Quotient) - prevents quotient forgery
//! 2. Circuit Linearity - enables Baked Quotient strategy  
//! 3. Full Span Separation (U, V, W verified) - blocks all PK-based attacks
//! 4. Aggregation - prevents GT-Slicing attacks
//!
//! ## Audit Checks
//!
//! 1. **Linearity Check**: Verifies that Public Inputs do not multiply each other.
//! 2. **Span Separation Check**: Verifies U/V/W_pub ⊥ U/V/W_wit (critical for security!)
//! 3. **Independence Check**: Verifies target is outside adversary's span in AGBGM.
//!
//! ## Key Modeling Features
//!
//! - **Armed Handles Only**: All handles have deg_ρ=1
//! - **Span-Separated Pub/Wit**: Uses separate monomials (e.g., AlphaDeltaVPub vs AlphaDeltaVWit)
//!   to properly model algebraic orthogonality when span separation holds.
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
use std::collections::{BTreeMap, HashMap, HashSet};

type Fr = OuterFr;

// All handles/targets are multiplied by delta to clear denominators from L-queries.
// Base ring: F[alpha, beta, gamma, delta, rho, x]
//
// ARCHITECTURE: Standard Groth16 with Full Span Separation
// All handles are ARMED (deg_ρ = 1) since the KEM target has deg_ρ = 1.
//
// FULL SPAN SEPARATION (U, V, W)
// When span separation holds for ALL three polynomial types:
// - U_pub ⊥ U_wit, V_pub ⊥ V_wit, W_pub ⊥ W_wit
// The adversary cannot synthesize public components from witness handles.
// We model this by using SEPARATE monomials for Pub vs Wit.

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TrapdoorMonomial {
    // ============================================================
    // TARGET TERMS (Armed, deg_ρ = 1) - All PUBLIC polynomials!
    // ============================================================
    // Standard Groth16 extraction: e(A,B) - e(C,δ) = e(α,β) + e(IC(x), γ)
    // Since IC(x) = Σ x_i · (β·u_i + α·v_i + w_i)/γ, pairing with γ gives:
    //   e(IC(x), γ) = β·U_pub + α·V_pub + W_pub (γ cancels!)
    // So the target is: ρ·(α·β + β·U_pub + α·V_pub + W_pub)
    // Under δ-normalization: ρ·δ·(α·β + β·U_pub + α·V_pub + W_pub)
    AlphaBetaDelta, // ρ * alpha * beta * delta (fixed)

    // ============================================================
    // SPAN-SEPARATED TARGET COMPONENTS (Pub vs Wit)
    // ============================================================
    // These are DISTINCT monomials when span separation holds.
    // The target uses PUBLIC polynomials (U_pub, V_pub, W_pub).
    // L-query handles provide WITNESS polynomials (U_wit, V_wit, W_wit).
    // If span separation holds, witness handles CANNOT synthesize target.
    
    // β·δ·U components
    BetaDeltaUPub, // ρ * beta * delta * U_pub (TARGET component)
    BetaDeltaUWit, // ρ * beta * delta * U_wit (from witness L-queries)
    
    // α·δ·V components
    AlphaDeltaVPub, // ρ * alpha * delta * V_pub (from bundled α handle + TARGET)
    AlphaDeltaVWit, // ρ * alpha * delta * V_wit (from witness L-queries)
    
    // δ·W components  
    DeltaWPub, // ρ * delta * W_pub (TARGET component)
    DeltaWWit, // ρ * delta * W_wit (from witness L-queries)

    // ============================================================
    // HANDLE TERMS from L_k * D_pub (Armed, deg_ρ = 1)
    // ============================================================
    // These are from WITNESS L-queries, so they use witness polynomials
    BetaSqU,    // ρ * beta^2 * u_wit
    BetaU,      // ρ * beta * u_wit * V
    AlphaBetaV, // ρ * alpha * beta * v_wit (available in standard Groth16)
    AlphaV,     // ρ * alpha * v_wit * V (available in standard Groth16)
    BetaW,      // ρ * beta * w_wit
    W,          // ρ * w_wit * V

    // Result is (beta*u + alpha*v + w)(v_j) - full L-query
    BetaUV,  // ρ * beta * u_wit * v
    AlphaVV, // ρ * alpha * v_wit * v (available in standard Groth16)
    WV,      // ρ * w_wit * v

    // ============================================================
    // OTHER HANDLE TERMS (Armed, deg_ρ = 1)
    // ============================================================
    DeltaUV,     // ρ * delta * u * V
    DeltaPureUV, // ρ * delta * u * v
    AlphaDeltaSq, // ρ * alpha * delta^2
    BetaV,       // ρ * v * beta
    PureVV,      // ρ * v * v
    
    // ============================================================
    // δ²·polynomial TERMS (Armed, deg_ρ = 1)
    // ============================================================
    // δ²·u ≠ δ²·v ≠ δ² (they're algebraically distinct directions!)
    // 
    // In PVUGC:
    // - Public A-queries are zeroed (u_pub = 0), so only DeltaSqUWit needed
    // - Public B-queries are NOT zeroed (v_pub ≠ 0), so we need BOTH Pub and Wit
    DeltaSqUWit, // ρ * delta^2 * u_wit (from e(u_k, δ^ρ), k >= num_pub)
    DeltaSqVPub, // ρ * delta^2 * v_pub (from e(v_k, δ^ρ), k < num_pub)
    DeltaSqVWit, // ρ * delta^2 * v_wit (from e(v_k, δ^ρ), k >= num_pub)
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

/// TEST CIRCUIT: V Span Separation SHOULD FAIL
/// For v_pub ∈ span(v_wit), we need v_pub = c * v_wit (scalar multiple).
/// 
/// SIMPLE: Put x and w in B at EXACTLY the same single row.
/// Then v_x = L_0 and v_w = L_0, so v_x = 1 * v_w.
struct MockSpanViolation;
impl AuditSubject for MockSpanViolation {
    fn name(&self) -> &'static str {
        "Mock V-Span Violation (SHOULD FAIL V-span)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;  // public
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?; // witness
        let one = Variable::One;
        
        // SINGLE constraint that puts BOTH x and w in B at row 0:
        // A=1, B=(x+w), C=2
        // This gives: v_x = L_0 and v_w = L_0
        // So v_x = 1 * v_w → v_pub IS IN span(v_wit)!
        let lc_a = LinearCombination::from((Fr::one(), one));
        let mut lc_b = LinearCombination::zero();
        lc_b += (Fr::one(), x);  // x in B at row 0
        lc_b += (Fr::one(), w);  // w in B at row 0 (SAME ROW!)
        let lc_c = LinearCombination::from((Fr::from(2u64), one));
        cs.enforce_constraint(lc_a, lc_b, lc_c)?;
        
        // Add a dummy constraint to satisfy minimum circuit requirements
        // 1 * 1 = 1
        let lc_a2 = LinearCombination::from((Fr::one(), one));
        let lc_b2 = LinearCombination::from((Fr::one(), one));
        let lc_c2 = LinearCombination::from((Fr::one(), one));
        cs.enforce_constraint(lc_a2, lc_b2, lc_c2)?;
        
        Ok(())
    }
}

/// TEST CIRCUIT: U Span Separation SHOULD FAIL
/// Put x and w in A at same row (so u_x = u_w).
/// Note: This also needs x in B for statement dependence.
struct MockUSpanViolation;
impl AuditSubject for MockUSpanViolation {
    fn name(&self) -> &'static str {
        "Mock U-Span Violation (SHOULD FAIL U-span)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;  // public
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?; // witness
        let one = Variable::One;
        
        // Constraint 0: Put BOTH x and w in A at SAME row
        // A=(x+w), B=1, C=(x+w)
        // This gives: u_x = L_0 and u_w = L_0
        // So u_x = 1 * u_w → u_pub IS IN span(u_wit)!
        let mut lc_a0 = LinearCombination::zero();
        lc_a0 += (Fr::one(), x);  // x in A at row 0
        lc_a0 += (Fr::one(), w);  // w in A at row 0 (SAME ROW!)
        let lc_b0 = LinearCombination::from((Fr::one(), one));
        let mut lc_c0 = LinearCombination::zero();
        lc_c0 += (Fr::one(), x);
        lc_c0 += (Fr::one(), w);
        cs.enforce_constraint(lc_a0, lc_b0, lc_c0)?;
        
        // Constraint 1: Put x in B for statement dependence (separate row)
        // 1 * x = x
        let lc_a1 = LinearCombination::from((Fr::one(), one));
        let lc_b1 = LinearCombination::from((Fr::one(), x));
        let lc_c1 = LinearCombination::from((Fr::one(), x));
        cs.enforce_constraint(lc_a1, lc_b1, lc_c1)?;
        
        Ok(())
    }
}

/// TEST CIRCUIT: W Span Separation SHOULD FAIL (but V should pass)
/// Put x and w in C at same row (so w_x = w_w), but x in B at different row than w.
struct MockWSpanViolation;
impl AuditSubject for MockWSpanViolation {
    fn name(&self) -> &'static str {
        "Mock W-Span Violation (SHOULD FAIL W-span, V-span OK)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?;
        let one = Variable::One;
        
        // Constraint 0: Put x in B (for statement dependence) but NOT where w is in B
        // 1 * x = 1  → v_x = L_0
        let lc_a0 = LinearCombination::from((Fr::one(), one));
        let lc_b0 = LinearCombination::from((Fr::one(), x));
        let lc_c0 = LinearCombination::from((Fr::one(), one));
        cs.enforce_constraint(lc_a0, lc_b0, lc_c0)?;
        
        // Constraint 1: Put BOTH x and w in C at SAME row
        // 1 * 1 = x + w  → w_x = L_1 and w_w = L_1
        // So w_x = 1 * w_w → w_pub IS IN span(w_wit)!
        let lc_a1 = LinearCombination::from((Fr::one(), one));
        let lc_b1 = LinearCombination::from((Fr::one(), one));
        let mut lc_c1 = LinearCombination::zero();
        lc_c1 += (Fr::one(), x);  // x in C at row 1
        lc_c1 += (Fr::one(), w);  // w in C at row 1 (SAME ROW!)
        cs.enforce_constraint(lc_a1, lc_b1, lc_c1)?;
        
        Ok(())
    }
}

fn main() {
    println!("PVUGC Production Audit Tool");
    println!("===========================\n");

    let subjects: Vec<Box<dyn AuditSubject>> = vec![
        Box::new(MockLinear),
        Box::new(MockQuadratic),
        Box::new(MockSpanViolation),    // Should FAIL V-span
        Box::new(MockUSpanViolation),   // Should FAIL U-span
        Box::new(MockWSpanViolation),   // Should FAIL W-span
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
    // With public inputs in C (not B), the architecture is:
    //   - u_pub = 0 (public not in A) ✓
    //   - v_pub = 0 (public not in B) ✓ NEW: This is now DESIRED
    //   - w_pub ≠ 0 (public IS in C) - provides statement binding via IC_i = w_i/γ
    let mut public_inputs_a_zero = true; // Columns 1..num_pub (actual public inputs)
    let mut public_inputs_b_zero = true; // Columns 1..num_pub should be B-free (NEW!)
    let mut public_inputs_c_nonzero = true; // Columns 1..num_pub MUST be in C
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
                "  [FAIL] Column {} has A entries! Public inputs must be A-free (u_pub=0).",
                i
            );
        }

        if b_count > 0 {
            public_inputs_b_zero = false;
            println!(
                "  [WARN] Column {} has B entries. For optimal security, public inputs should be C-only (v_pub=0).",
                i
            );
        }

        if c_count == 0 {
            public_inputs_c_nonzero = false;
            println!(
                "  [FAIL] Column {} has C=0! Public inputs must be in C for statement binding (w_pub≠0).",
                i
            );
        }

        // Check if IC_i would be zero (security issue!)
        // With public in C only: IC_i = w_i/γ, so w_i must be non-zero
        if c_count == 0 {
            println!(
                "  [SECURITY] Column {} has w_i=0 → IC_i=0 → PUBLIC INPUT NOT BOUND!",
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

    // New architecture: public in C, not B
    if public_inputs_a_zero && public_inputs_b_zero && public_inputs_c_nonzero {
        println!("[PASS] Public input structure valid (A=0, B=0, C>0) → Optimal Lean CRS");
        println!("       → No (wit,pub) cross-terms in quotient");
        println!("       → Statement binding via W-polynomial (IC_i = w_i/γ)");
    } else if public_inputs_a_zero && public_inputs_c_nonzero {
        println!("[PASS] Public input structure acceptable (A=0, C>0) → Statement Dependent");
        if !public_inputs_b_zero {
            println!("       [NOTE] B≠0 creates (wit,pub) quotient pairs - consider moving to C-only");
        }
    } else {
        println!("[FAIL] Public input structure INVALID");
        if !public_inputs_a_zero {
            println!("       → A≠0 violates one-sided property!");
        }
        if !public_inputs_c_nonzero {
            println!("       → C=0 means no statement binding!");
        }
    }
    
    // === DECISIVE SPAN MEMBERSHIP TEST ===
    // Verify Q_const ∉ span(H_{ij})
    // This is the "gold standard" check for quotient reachability
    let span_test_passed = verify_public_only_in_c_and_w_span_separated(&extractor, num_pub, num_wit);

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

    // Instance assignment vector (including column 0). This is the actual
    // public input assignment used to weight U/V/W_pub in the target and
    // in D_pub. We require it to match num_pub.
    let instance = cs
        .borrow()
        .expect("cs should be available")
        .instance_assignment
        .clone();
    assert_eq!(
        instance.len(),
        num_pub,
        "instance_assignment length must equal num_pub"
    );

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

    // 1.6 Span Separation Checks (U_pub ⊥ U_wit, V_pub ⊥ V_wit, W_pub ⊥ W_wit)
    println!("\n--- Span Separation Analysis ---");
    
    // V (B-matrix) - CRITICAL for α-handle attack
    let v_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "V", "B",
        |e, i| &e.b_cols[i],
    );
    if v_span_separated {
        println!("[PASS] V Span Separation (V_pub ⊥ V_wit) → α-handle attack blocked.");
    } else {
        println!("[FAIL] V Span Separation (V_pub ∈ span V_wit) → Lean CRS required!");
    }
    
    // U (A-matrix) - for L-query derived β·U attacks
    let u_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "U", "A",
        |e, i| &e.a_cols[i],
    );
    if u_span_separated {
        println!("[PASS] U Span Separation (U_pub ⊥ U_wit) → β·U synthesis blocked.");
    } else {
        println!("[WARN] U Span Separation failed (U_pub ∈ span U_wit) → L-query risk.");
    }
    
    // W (C-matrix) - for L-query derived W attacks
    let w_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "W", "C",
        |e, i| &e.c_cols[i],
    );
    if w_span_separated {
        println!("[PASS] W Span Separation (W_pub ⊥ W_wit) → W synthesis blocked.");
    } else {
        println!("[WARN] W Span Separation failed (W_pub ∈ span W_wit) → L-query risk.");
    }
    
    // Combined span separation result
    let full_span_separated = v_span_separated && u_span_separated && w_span_separated;
    
    println!("--- End Span Separation ---\n");

    // 2. Independence Check (Lean CRS: no explicit H·δ² quotient direction)
    let target = build_target(&pub_polys, &instance);

    // Use multiple random evaluation points for robustness of the independence check.
    let num_checks = 4;
    let all_safe = run_independence_checks(
        "",
        &extractor,
        &pub_polys,
        &instance,
        &target,
        num_pub + num_wit,
        num_checks,
    );

    // Final verdict
    let fully_safe = is_linear && is_unmixed && all_safe && no_pub_ab_overlap;
    
    println!("\n=== SECURITY SUMMARY (AGBGM) ===");
    println!("Linearity:          {}", if is_linear { "PASS" } else { "FAIL" });
    println!("No Pub/Wit Mix:     {}", if is_unmixed { "PASS" } else { "FAIL" });
    println!("No Pub A/B Overlap: {}", if no_pub_ab_overlap { "PASS" } else { "FAIL" });
    println!("V Span Separation:  {}", if v_span_separated { "PASS" } else { "FAIL" });
    println!("U Span Separation:  {}", if u_span_separated { "PASS" } else { "FAIL" });
    println!("W Span Separation:  {}", if w_span_separated { "PASS" } else { "FAIL" });
    println!("Independence:       {}", if all_safe { "PASS" } else { "FAIL" });
    
    // Full span separation is THE critical security property
    if full_span_separated {
        println!("\n✅ FULL SPAN SEPARATION VERIFIED (U, V, W all orthogonal)!");
        println!("");
        println!("   This enables STANDARD GROTH16 architecture:");
        println!("   • Standard L-queries are SAFE");
        println!("   • Standard IC algebra");
        println!("   • Standard decap works (proof-agnostic key extraction)");
        println!("");
        println!("   Attack blocking (AGBGM verified):");
        println!("   • V-span blocks: e([α]_1, D_pub^ρ) pollution cancellation");
        println!("   • U-span blocks: β·U_pub synthesis from witness L-queries");
        println!("   • W-span blocks: W_pub synthesis from witness L-queries");
    } else {
        if !v_span_separated {
            println!("\n⚠️  V SPAN SEPARATION FAILED!");
            println!("   V_pub ∈ span(V_wit), so:");
            println!("   • e([α]_1, D_pub^ρ) pollution CAN be cancelled");
            println!("   • MUST use Lean CRS (remove [α]_1 from public PK)");
        }
        
        if !u_span_separated || !w_span_separated {
            println!("\n⚠️  U/W SPAN SEPARATION FAILED!");
            println!("   Residue synthesis attack possible:");
            println!("   • e(L_k, δ^ρ) gives ρ·(β·u_k + w_k)");
            println!("   • If U_pub or W_pub in witness span, can synthesize target");
            println!("   • This is a fundamental issue - circuit redesign may be needed");
        }
    }

    println!(
        "\nRESULT: {}",
        if fully_safe && full_span_separated {
            "✅ SECURE (Standard Groth16 with Full Span Separation)"
        } else if fully_safe {
            "⚠️  CONDITIONALLY SAFE (requires additional mitigations)"
        } else {
            "❌ UNSAFE"
        }
    );
    
    if fully_safe && full_span_separated {
        println!("\n=== MINIMAL REQUIRED ARCHITECTURE ===");
        println!("1. Lean CRS (Baked Quotient) - quotient forgery prevention");
        println!("2. Circuit Linearity - verified above");
        println!("3. Full Span Separation - verified above");
        println!("4. Aggregation - prevents GT-Slicing (verify separately)");
    }
}

fn check_public_ab_overlap(extractor: &MatrixExtractor, num_pub: usize) -> bool {
    for col in 1..num_pub {
        // Work with net coefficients per row to avoid false flags from +c/-c pairs.
        let a_net = to_sparse_row_vec(&extractor.a_cols[col]);
        let b_net = to_sparse_row_vec(&extractor.b_cols[col]);
        if a_net.is_empty() || b_net.is_empty() {
            continue;
        }
        let rows_b: HashSet<usize> = b_net.keys().copied().collect();
        for row in a_net.keys() {
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



/// Decisive structural check for the "public-only-in-C" architecture.
///
/// Interpreting `num_pub` as `cs.num_instance_variables()` (includes ONE at index 0),
/// and `num_wit` as `cs.num_witness_variables()`.
///
/// This is the check you want to hang the proof sketch on:
///   1) u_pub = 0  (public wires never appear in A)
///   2) v_pub = 0  (public wires never appear in B)
///   3) statement binding sanity: public wires appear in C (otherwise R(vk,x) won't vary with x)
///   4) W-span separation: rows(C_pub) ∩ rows(C_wit) = ∅
///
/// If all hold, then under your hardened-arming/lean-CRS model:
///   - published H_ij are witness-only quotient directions
///   - Q_const is a pure public-C quotient direction
///   - so Q_const is unreachable from published H_ij handles.
fn verify_public_only_in_c_and_w_span_separated(
    extractor: &MatrixExtractor,
    num_pub: usize,
    num_wit: usize,
) -> bool {
    let num_vars = num_pub + num_wit;

    // Basic shape sanity.
    assert_eq!(extractor.a_cols.len(), num_vars, "a_cols len mismatch");
    assert_eq!(extractor.b_cols.len(), num_vars, "b_cols len mismatch");
    assert_eq!(extractor.c_cols.len(), num_vars, "c_cols len mismatch");

    println!("=== Span Membership Test (Quotient Reachability) ===");

    // 1) u_pub = 0 for all public cols 1..num_pub-1 (0 is ONE).
    let mut u_pub_nonzero: Vec<(usize, usize)> = Vec::new();
    for col in 1..num_pub {
        let a_entries = &extractor.a_cols[col];
        if !a_entries.is_empty() {
            u_pub_nonzero.push((col, a_entries.len()));
        }
    }
    if u_pub_nonzero.is_empty() {
        println!(
            "  [Span] PASS: u_pub = 0 - No public columns (1..{}) in A-matrix",
            num_pub.saturating_sub(1)
        );
    } else {
        for (col, nnz) in &u_pub_nonzero {
            println!(
                "  [Span] FAIL: u_pub ≠ 0 - Public column {} has {} A-matrix entries",
                col, nnz
            );
        }
    }

    // 2) v_pub = 0 for all public cols 1..num_pub-1.
    let mut v_pub_nonzero: Vec<(usize, usize)> = Vec::new();
    for col in 1..num_pub {
        let b_entries = &extractor.b_cols[col];
        if !b_entries.is_empty() {
            v_pub_nonzero.push((col, b_entries.len()));
        }
    }
    if v_pub_nonzero.is_empty() {
        println!(
            "  [Span] PASS: v_pub = 0 - No public columns (1..{}) in B-matrix",
            num_pub.saturating_sub(1)
        );
    } else {
        for (col, nnz) in &v_pub_nonzero {
            println!(
                "  [Span] FAIL: v_pub ≠ 0 - Public column {} has {} B-matrix entries",
                col, nnz
            );
        }
    }

    // 2.5) Binding sanity: each public column should appear in C at least once
    // (otherwise the statement doesn't actually affect IC(x) via C).
    let mut c_pub_missing: Vec<usize> = Vec::new();
    for col in 1..num_pub {
        let c_entries = &extractor.c_cols[col];
        if c_entries.is_empty() {
            c_pub_missing.push(col);
        }
    }
    if c_pub_missing.is_empty() {
        println!(
            "  [Bind] PASS: every public column (1..{}) appears in C at least once",
            num_pub.saturating_sub(1)
        );
    } else {
        println!(
            "  [Bind] FAIL: public columns missing from C: {:?}",
            c_pub_missing
        );
    }

    // 3) W-span separation: rows(C_pub) ∩ rows(C_wit) = ∅
    let mut w_pub_rows: HashSet<usize> = HashSet::new();
    for col in 1..num_pub {
        for &(row, _) in &extractor.c_cols[col] {
            w_pub_rows.insert(row);
        }
    }

    let mut w_wit_rows: HashSet<usize> = HashSet::new();
    for col in num_pub..num_vars {
        for &(row, _) in &extractor.c_cols[col] {
            w_wit_rows.insert(row);
        }
    }

    let mut shared: Vec<usize> = w_pub_rows.intersection(&w_wit_rows).copied().collect();
    shared.sort_unstable();

    let w_sep = shared.is_empty();
    if w_sep {
        println!("  [Span] PASS: W-span separation - W_pub and W_wit have disjoint row support");
        println!("         W_pub rows: {}, W_wit rows: {}", w_pub_rows.len(), w_wit_rows.len());
    } else {
        println!("  [Span] FAIL: W-span overlap - {} shared rows", shared.len());
        let show = shared.len().min(10);
        println!("         Shared rows (first {}): {:?}", show, &shared[..show]);
    }

    let passed = u_pub_nonzero.is_empty()
        && v_pub_nonzero.is_empty()
        && c_pub_missing.is_empty()
        && w_sep;

    if passed {
        println!("\n  --- Span Membership Verdict ---");
        println!("  u_pub=0, v_pub=0 ⇒ published H_ij are witness-only (A_wit·B_wit)/Z directions.");
        println!("  W_pub ⟂ W_wit ⇒ the baked Q_const lives in a disjoint public-C quotient direction.");
        println!("  Therefore Q_const ∉ span(H_ij), so T_const^ρ is unreachable via e(·, δ^ρ).");
        println!("[PASS] DECISIVE: Q_const ∉ span(H_{{ij}})");
        println!("       → Adversary CANNOT synthesize T_const^ρ from e(H_ij, δ^ρ)");
    } else {
        println!("[FAIL] Span membership check failed - potential security issue!");
    }

    passed
}


fn check_mixing(extractor: &MatrixExtractor, num_pub: usize, num_vars: usize) -> bool {
    let domain_size = extractor.domain.size();
    let mut rows_pub_a = vec![false; domain_size];
    let mut rows_pub_b = vec![false; domain_size];

    // Mark rows where Public Inputs (excluding 1) appear in A and B
    for i in 1..num_pub {
        let a_net = to_sparse_row_vec(&extractor.a_cols[i]);
        let b_net = to_sparse_row_vec(&extractor.b_cols[i]);
        for (&row, _) in a_net.iter() {
            rows_pub_a[row] = true;
        }
        for (&row, _) in b_net.iter() {
            rows_pub_b[row] = true;
        }
    }

    // Check Witness columns
    for j in num_pub..num_vars {
        let a_net = to_sparse_row_vec(&extractor.a_cols[j]);
        let b_net = to_sparse_row_vec(&extractor.b_cols[j]);
        // If Witness in A, check if Row has Public in B
        for (&row, _) in a_net.iter() {
            if rows_pub_b[row] {
                return false;
            }
        }
        // If Witness in B, check if Row has Public in A
        for (&row, _) in b_net.iter() {
            if rows_pub_a[row] {
                return false;
            }
        }
    }
    true
}

/// Generalized Span Separation Check for any matrix (A, B, or C)
/// 
/// Checks if public polynomial P_pub is NOT in span of witness polynomials P_wit.
/// Uses direct row-overlap check for reliability.
/// 
/// Parameters:
/// - matrix_name: "U", "V", or "W" for display
/// - col_name: "A", "B", or "C" for display  
/// - get_col: closure to get column entries from extractor
///
/// This uses an exact sparse Gaussian-elimination check in Lagrange
/// coefficient space (no random sampling), so results are deterministic and
/// not sensitive to the number of witness columns.
type SparseRowVec = BTreeMap<usize, Fr>;

/// Convert a sparse column representation (row, coeff) into a sparse row vector
/// backed by a BTreeMap. Zero coefficients are dropped.
fn to_sparse_row_vec(entries: &Vec<(usize, Fr)>) -> SparseRowVec {
    let mut v = SparseRowVec::new();
    for (row, coeff) in entries {
        if !coeff.is_zero() {
            let entry = v.entry(*row).or_insert(Fr::zero());
            *entry += *coeff;
            if entry.is_zero() {
                v.remove(row);
            }
        }
    }
    v
}

/// Sparse row-basis over the QAP domain.
///
/// Each basis vector is stored in row-sparse form and normalized so that its
/// pivot row has coefficient 1. This lets us do exact linear dependence checks
/// in Lagrange coefficient space without any random sampling.
struct RowBasis {
    /// pivot_row -> normalized sparse vector with pivot_row coefficient = 1
    pivots: BTreeMap<usize, SparseRowVec>,
}

impl RowBasis {
    fn new() -> Self {
        Self {
            pivots: BTreeMap::new(),
        }
    }

    /// Reduce v using the current basis (Gaussian elimination over sparse rows).
    /// Returns the residue v', which is zero iff v is in the span of the basis.
    fn reduce(&self, mut v: SparseRowVec) -> SparseRowVec {
        for (&p, pv) in self.pivots.iter() {
            if let Some(&coeff) = v.get(&p) {
                if !coeff.is_zero() {
                    // v -= coeff * pv
                    for (&r, &c) in pv.iter() {
                        let entry = v.entry(r).or_insert(Fr::zero());
                        *entry -= coeff * c;
                        if entry.is_zero() {
                            v.remove(&r);
                        }
                    }
                }
            }
        }
        v
    }

    /// Insert a new vector into the basis (if it is not already in the span).
    fn insert(&mut self, v: SparseRowVec) {
        let mut v = self.reduce(v);
        // Find first non-zero entry as pivot (smallest row index).
        if let Some((&pivot_row, &pivot_coeff)) = v.iter().next() {
            // Normalize so that pivot coefficient is 1.
            let inv = pivot_coeff.inverse().unwrap();
            for coeff in v.values_mut() {
                *coeff *= inv;
            }

            // Eliminate this pivot from existing basis vectors to keep them reduced.
            let mut rows_to_update = Vec::new();
            for (&existing_pivot, existing_vec) in self.pivots.iter() {
                if existing_vec.contains_key(&pivot_row) {
                    rows_to_update.push(existing_pivot);
                }
            }

            for row in rows_to_update {
                if let Some(mut existing_vec) = self.pivots.remove(&row) {
                    let coeff = *existing_vec
                        .get(&pivot_row)
                        .expect("pivot row must be present");
                    if !coeff.is_zero() {
                        for (&r, &c) in v.iter() {
                            let entry = existing_vec.entry(r).or_insert(Fr::zero());
                            *entry -= coeff * c;
                            if entry.is_zero() {
                                existing_vec.remove(&r);
                            }
                        }
                    }
                    // Re-insert only if non-zero
                    if !existing_vec.is_empty() {
                        self.pivots.insert(row, existing_vec);
                    }
                }
            }

            // Finally, insert the new basis vector.
            self.pivots.insert(pivot_row, v);
        }
    }
}

fn check_span_separation_matrix<F>(
    extractor: &MatrixExtractor, 
    num_pub: usize, 
    num_vars: usize,
    matrix_name: &str,
    col_name: &str,
    get_col: F,
) -> bool 
where
    F: Fn(&MatrixExtractor, usize) -> &Vec<(usize, Fr)>,
{
    let num_wit = num_vars - num_pub;
    if num_wit == 0 {
        println!("  [{}_SPAN] No witness columns to check.", matrix_name);
        return true;
    }
    
    // Collect all rows where ACTUAL public input columns (1..num_pub) have entries.
    // NOTE: Column 0 is the constant "ONE" wire, NOT a public input.
    // We skip it here because ONE doesn't carry statement-dependent information.
    let mut pub_rows: HashSet<usize> = HashSet::new();
    for i in 1..num_pub {
        let v = to_sparse_row_vec(get_col(extractor, i));
        for (&row, _) in v.iter() {
            pub_rows.insert(row);
        }
    }
    
    // Log constant column stats separately for clarity
    let one_entries = get_col(extractor, 0);
    if !one_entries.is_empty() {
        println!("  [{}_SPAN] Note: Constant '1' (col 0) has {} {}-entries (excluded from pub/wit check)", 
                 matrix_name, one_entries.len(), col_name);
    }
    
    if pub_rows.is_empty() {
        println!("  [{}_SPAN] Public inputs (cols 1..{}) have no {}-entries ({}_pub = 0). Trivially separated.", 
                 matrix_name, num_pub.saturating_sub(1), col_name, matrix_name.to_lowercase());
        return true;
    }
    
    println!("  [{}_SPAN] Public inputs (cols 1..{}) have {}-entries at {} rows: {:?}", 
             matrix_name, num_pub.saturating_sub(1), col_name, pub_rows.len(), 
             pub_rows.iter().take(5).collect::<Vec<_>>());
    
    // Check if ANY witness column has entries at those same rows (using net
    // coefficients per row to avoid +c/-c artifacts).
    let mut overlapping_witnesses: Vec<(usize, Vec<usize>)> = Vec::new();
    
    for j in num_pub..num_vars {
        let mut overlap_rows: Vec<usize> = Vec::new();
        let v = to_sparse_row_vec(get_col(extractor, j));
        for (&row, _) in v.iter() {
            if pub_rows.contains(&row) {
                overlap_rows.push(row);
            }
        }
        if !overlap_rows.is_empty() {
            overlapping_witnesses.push((j, overlap_rows));
        }
    }
    
    if overlapping_witnesses.is_empty() {
        println!(
            "  [{}_SPAN] No witness {}-entries overlap with public {}-rows.", 
            matrix_name, col_name, col_name
        );
        println!(
            "  [{}_SPAN] By Lagrange orthogonality: {}_pub NOT in span({}_wit)", 
            matrix_name,
            matrix_name.to_lowercase(),
            matrix_name.to_lowercase()
        );
        return true;
    }
    
    // There ARE overlapping witnesses - need full span check in coefficient space.
    // Example: p on {r1}, w1 on {r1,r2}, w2 on {r2} -> p = w1 - w2 is in span.
    println!(
        "  [{}_SPAN] {} witness columns have {}-entries overlapping public rows", 
        matrix_name,
        overlapping_witnesses.len(),
        col_name
    );

    // Build a sparse row-basis from ALL witness columns in this matrix.
    let mut wit_basis = RowBasis::new();
    for j in num_pub..num_vars {
        let entries = get_col(extractor, j);
        if entries.is_empty() {
            continue;
        }
        let v = to_sparse_row_vec(entries);
        if !v.is_empty() {
            wit_basis.insert(v);
        }
    }

    let mut all_separated = true;
    // Only check actual public input columns (1..num_pub), NOT constant column 0
    let pub_cols_to_check = 1..num_pub;
    let num_pub_to_check = num_pub.saturating_sub(1);

    // Build a basis for the public span and for its image modulo the witness
    // span. We require dim(span(P_pub) mod span(P_wit)) == dim(span(P_pub)).
    let mut pub_basis = RowBasis::new();
    let mut pub_reduced_basis = RowBasis::new();

    for (idx, i) in pub_cols_to_check.enumerate() {
        let pub_vec = to_sparse_row_vec(get_col(extractor, i));
        if pub_vec.is_empty() {
            // Net-zero column: trivially separated
            continue;
        }
        pub_basis.insert(pub_vec.clone());
        let reduced = wit_basis.reduce(pub_vec);
        if reduced.is_empty() {
            println!(
                "  [{}_SPAN FAIL] Public column {} is IN span of witness columns", 
                matrix_name, i
            );
            all_separated = false;
            // No need to keep going; we already know there's overlap.
            continue;
        }
        pub_reduced_basis.insert(reduced);

        // Progress for public columns (purely cosmetic)
        if (idx + 1) % 5 == 0 || idx + 1 == num_pub_to_check {
            print!(
                "\r  [{}_SPAN] Checking public columns (exact): {}/{}...", 
                matrix_name,
                idx + 1,
                num_pub_to_check
            );
            use std::io::Write;
            let _ = std::io::stdout().flush();
        }
    }
    if num_pub_to_check > 0 {
        println!(" done");
    }

    // If every non-zero public column survived reduction but their reduced span
    // has lower rank than the original public span, then some nontrivial
    // public combination lies in the witness span.
    if all_separated {
        let rank_pub = pub_basis.pivots.len();
        let rank_img = pub_reduced_basis.pivots.len();
        if rank_img < rank_pub {
            println!(
                "  [{}_SPAN FAIL] Some nontrivial public combination lies in witness span (rank {} < {}).",
                matrix_name,
                rank_img,
                rank_pub
            );
            return false;
        }
    }

    all_separated
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
        // CRITICAL: Domain must match the Groth16/QAP domain used in proving.
        // Standard Groth16 uses a domain of size (num_constraints + num_inputs),
        // padded up to the nearest supported FFT size if necessary. Mirror the
        // logic from `compute_witness_bases` so the audit sees the same U/V/W
        // polynomials as the real prover.
        let num_constraints = cs.num_constraints();
        let num_inputs = cs.num_instance_variables(); // includes constant 1
        let qap_domain_size = num_constraints + num_inputs;
        let domain = GeneralEvaluationDomain::<Fr>::new(qap_domain_size)
            .or_else(|| GeneralEvaluationDomain::<Fr>::new(qap_domain_size.next_power_of_two()))
            .expect("domain");
        let domain_size = domain.size();

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
            u_evals[row] += val;
        }
        for &(row, val) in &self.b_cols[col] {
            v_evals[row] += val;
        }
        for &(row, val) in &self.c_cols[col] {
            w_evals[row] += val;
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
            let mut root_sum: Option<Fr> = None;
            for &(row, val) in sparse {
                let omega_i = self.domain.element(row);
                let denom = r - omega_i;
                if denom.is_zero() {
                    // r coincides with a domain point ω_i where the column has value `val`.
                    // Multiple entries on the same row must be summed.
                    let s = root_sum.get_or_insert(Fr::zero());
                    *s += val;
                    // Once we know r is exactly a domain root for this column,
                    // the true value is determined by the sum at that root; we
                    // can ignore remaining entries.
                    continue;
                }
                // Only accumulate barycentric terms when we have not hit a root.
                // If r == ω_k for some k, the true value is just the sum of coeffs at row k.
                if root_sum.is_none() {
                    acc += (val * omega_i) * denom.inverse().unwrap();
                }
            }
            if let Some(s) = root_sum {
                s
            } else {
                acc * common
            }
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

fn build_target(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    pub_coeffs: &[Fr],
) -> TrapdoorPolyVector {
    // Reconstruct L_pub components
    // L_pub = Sum x_i (beta u_i + alpha v_i + w_i)
    // Normalized Target (x delta) = alpha*beta*delta + delta * L_pub
    // = alpha*beta*delta + beta*delta*U + alpha*delta*V + delta*W

    let mut u_sum = DensePolynomial::zero();
    let mut v_sum = DensePolynomial::zero();
    let mut w_sum = DensePolynomial::zero();

    // Weighted sums: U_pub = Σ a_i u_i, V_pub = Σ a_i v_i, W_pub = Σ a_i w_i
    // where a_i are the instance assignments (including column 0).
    assert_eq!(pub_polys.len(), pub_coeffs.len());
    for ((u, v, w), a_i) in pub_polys.iter().zip(pub_coeffs.iter()) {
        if a_i.is_zero() {
            continue;
        }
        let a = *a_i;
        u_sum += &(&*u * a);
        v_sum += &(&*v * a);
        w_sum += &(&*w * a);
    }

    // TARGET uses PUBLIC polynomials (U_pub, V_pub, W_pub) from standard IC(x)
    // These are span-separated from witness polynomials.
    TrapdoorPolyVector::new(vec![
        (
            TrapdoorMonomial::AlphaBetaDelta,
            DensePolynomial::from_coefficients_slice(&[Fr::one()]),
        ),
        (TrapdoorMonomial::BetaDeltaUPub, u_sum),   // β·δ·U_pub
        (TrapdoorMonomial::AlphaDeltaVPub, v_sum),  // α·δ·V_pub
        (TrapdoorMonomial::DeltaWPub, w_sum),       // δ·W_pub
    ])
}

/// Dense basis over the abstract monomial space used for independence checks.
///
/// We key rows by their pivot index in a BTreeMap so that reduction always
/// processes pivots in ascending order, avoiding order-dependent artifacts.
struct Basis {
    rows: BTreeMap<usize, Vec<Fr>>,
}

impl Basis {
    fn new() -> Self {
        Self {
            rows: BTreeMap::new(),
        }
    }

    fn reduce(&self, mut v: Vec<Fr>) -> Vec<Fr> {
        for (&pivot, row) in self.rows.iter() {
            if pivot >= v.len() {
                continue;
            }
            if !v[pivot].is_zero() {
                let factor = v[pivot];
                for k in pivot..v.len() {
                    v[k] -= factor * row[k];
                }
            }
        }
        v
    }

    fn insert(&mut self, v: Vec<Fr>) {
        let reduced = self.reduce(v);
        if let Some(pivot) = reduced.iter().position(|x| !x.is_zero()) {
            let inv = reduced[pivot].inverse().unwrap();
            let normalized: Vec<Fr> = reduced.iter().map(|x| *x * inv).collect();
            self.rows.insert(pivot, normalized);
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
    pub_coeffs: &[Fr],
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
        // Span-separated monomials (Pub vs Wit - critical for security!)
        TrapdoorMonomial::BetaDeltaUPub,
        TrapdoorMonomial::BetaDeltaUWit,
        TrapdoorMonomial::AlphaDeltaVPub,
        TrapdoorMonomial::AlphaDeltaVWit,
        TrapdoorMonomial::DeltaWPub,
        TrapdoorMonomial::DeltaWWit,
        // L-query handles (use witness polynomials)
        TrapdoorMonomial::BetaSqU,
        TrapdoorMonomial::BetaU,
        TrapdoorMonomial::AlphaBetaV,
        TrapdoorMonomial::AlphaV,
        TrapdoorMonomial::BetaW,
        TrapdoorMonomial::W,
        TrapdoorMonomial::BetaUV,
        TrapdoorMonomial::AlphaVV,
        TrapdoorMonomial::WV,
        TrapdoorMonomial::DeltaUV,
        TrapdoorMonomial::DeltaPureUV,
        TrapdoorMonomial::AlphaDeltaSq,
        TrapdoorMonomial::BetaV,
        TrapdoorMonomial::PureVV,
        // δ²·polynomial terms
        TrapdoorMonomial::DeltaSqUWit,
        TrapdoorMonomial::DeltaSqVPub,
        TrapdoorMonomial::DeltaSqVWit,
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
    assert_eq!(pub_polys.len(), pub_coeffs.len());
    for ((_, v, _), a_i) in pub_polys.iter().zip(pub_coeffs.iter()) {
        if a_i.is_zero() {
            continue;
        }
        v_pub_r += v.evaluate(&r) * a_i;
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

        // 1–3. Raw U-side handles from u_k:
        //
        // In the Lean CRS, public A-queries for true public inputs (columns 1..num_pub-1)
        // are zeroed in the proving key, and column 0 (constant "1") is treated as part
        // of the baked trapdoor (α), not as a U_wit direction. We therefore only model
        // these U_wit handles for k >= num_pub (witness columns).
        if k >= num_pub {
            // 1. u_k * D_pub * delta -> beta*delta*u + delta*u*V
            // Uses BetaDeltaUWit because only witness columns have non-zero A-queries.
            add_basis_vec(
                "u_k * D_pub * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaDeltaUWit, u_val),
                    (TrapdoorMonomial::DeltaUV, u_val * v_pub_r),
                ],
            );

            // 2. u_k * D_delta * delta -> u * delta^2 (under δ-normalization)
            // Actual: e([u_k]_1, [δ]_2^ρ) = ρ·δ·u_k
            // Normalized: δ · (ρ·δ·u_k) = ρ·δ²·u_k → DeltaSqUWit
            add_basis_vec(
                "u_k * D_delta * delta",
                k,
                vec![(TrapdoorMonomial::DeltaSqUWit, u_val)],
            );

            // 3. u_k * D_j * delta -> u * v_j * delta
            add_basis_vec(
                "u_k * D_j * delta",
                k,
                vec![(TrapdoorMonomial::DeltaPureUV, u_val)],
            );
        }

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
            // Uses WITNESS variants because L-queries only exist for k >= num_pub.
            add_basis_vec(
                "L_k * D_delta * delta (WITNESS)",
                k,
                vec![
                    (TrapdoorMonomial::BetaDeltaUWit, u_val), // WITNESS U
                    (TrapdoorMonomial::AlphaDeltaVWit, v_val), // WITNESS V
                    (TrapdoorMonomial::DeltaWWit, w_val),      // WITNESS W
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
        // Actual: e([v_k]_1, [δ]_2^ρ) = ρ·δ·v_k
        // Normalized: δ · (ρ·δ·v_k) = ρ·δ²·v_k
        // Use DeltaSqVPub for public columns, DeltaSqVWit for witness columns
        if k < num_pub {
            add_basis_vec("Raw B DeltaSqVPub", k, vec![(TrapdoorMonomial::DeltaSqVPub, v_val)]);
        } else {
            add_basis_vec("Raw B DeltaSqVWit", k, vec![(TrapdoorMonomial::DeltaSqVWit, v_val)]);
        }
        // v_k (G1) * beta (G2) -> v * beta
        add_basis_vec("Raw B BetaV", k, vec![(TrapdoorMonomial::BetaV, v_val)]);
        add_basis_vec("Raw B PureVV", k, vec![(TrapdoorMonomial::PureVV, v_val)]);
        
    }
    println!(
        "\r[Independence Check {}/{}] Progress: 100%",
        check_idx, total_checks
    );

    // 8. Alpha * D_pub (bundled) - from e([α]_1, y_cols_rho[0])
    // This is the BUNDLED handle: adversary gets AlphaBetaDelta + AlphaDeltaVPub together.
    // They CANNOT separate these components - they come as a package.
    //
    // KEY INSIGHT: With span separation (V_pub ⊥ V_wit):
    // - The adversary gets AlphaDeltaVPub bundled with AlphaBetaDelta
    // - The target ALSO includes AlphaDeltaVPub (from standard IC)
    // - So the bundled handle contributes directly to target!
    // - Security depends on the REMAINING target (BetaDeltaUPub, DeltaWPub)
    //   which CANNOT be synthesized from witness handles if span separation holds!
    add_basis_vec(
        "Alpha * y_cols_rho[0] (D_pub bundled)",
        usize::MAX,
        vec![
            (TrapdoorMonomial::AlphaBetaDelta, Fr::one()),
            (TrapdoorMonomial::AlphaDeltaVPub, v_pub_r),
        ],
    );

    // 9. Alpha * y_cols_rho[wit] - from e([α]_1, y_cols_rho[j]) for all witness j
    // The arming transcript includes ALL individual Y_j^ρ, so the adversary can
    // compute e([α]_1, [v_j]_2^ρ) = ρ·α·v_j for any witness column j.
    // This spans the full AlphaDeltaVWit direction.
    add_basis_vec(
        "Alpha * y_cols_rho[wit] (V_wit span)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaVWit, Fr::one())],
    );

    // 10. Alpha * delta_rho - from e([α]_1, delta_rho) = ρ·α·δ
    // Under δ-normalization this becomes ρ·α·δ² → AlphaDeltaSq
    add_basis_vec(
        "Alpha * delta_rho",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaSq, Fr::one())],
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
    pub_coeffs: &[Fr],
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
            pub_coeffs,
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
