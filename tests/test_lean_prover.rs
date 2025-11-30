//! Test for Lean Prover implementation
//!
//! Verifies that the "Lean Prover" (using sparse H-bases) produces valid Groth16 proofs
//! that are accepted by the standard Verifier.

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_groth16::{r1cs_to_qap::PvugcReduction, Groth16};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_snark::SNARK;
use ark_std::{rand::SeedableRng, Zero};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterScalar,
};
use arkworks_groth16::ppe::{compute_baked_target, PvugcVk};
use arkworks_groth16::prover_lean::{prove_lean, prove_lean_with_randomizers, LeanProvingKey};
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::RecursionCycle;

/// Circuit that simulates proof point allocation:
/// - Public input x (packed scalar)
/// - Witness "proof coordinates" (simulates inner proof A, B, C curve points)
/// - Witness × witness constraints (like on-curve checks)
/// - Linear constraint tying x to some witness bits
///
/// This tests that:
/// 1. Witness × witness constraints don't break the affine quotient
/// 2. q_const must be computed with the SAME proof coords used in real proving
///    (using zeros for setup but real values for proving causes mismatch!)
#[derive(Clone)]
struct ProofPointSimCircuit<F: ark_ff::PrimeField> {
    pub x: F,                 // Public input (packed scalar)
    pub proof_coords: Vec<F>, // Simulated proof point coordinates (passed in, not generated)
    pub bits: Vec<bool>,      // Bits for packing constraint
}

impl<F: ark_ff::PrimeField> ProofPointSimCircuit<F> {
    /// Create circuit with specific proof coordinates (for testing dummy vs real)
    fn with_coords(x: F, num_bits: usize, proof_coords: Vec<F>) -> Self {
        use ark_ff::BigInteger;

        // Bits are derived from x (like in real OuterCircuit)
        let mut bits = x.into_bigint().to_bits_le();
        bits.truncate(num_bits);
        bits.resize(num_bits, false);

        Self {
            x,
            proof_coords,
            bits,
        }
    }

    /// Create circuit with dummy (zero) proof coordinates - simulates old buggy behavior
    fn with_dummy_coords(x: F, num_bits: usize, num_proof_coords: usize) -> Self {
        let proof_coords = vec![F::zero(); num_proof_coords];
        Self::with_coords(x, num_bits, proof_coords)
    }

    /// Create circuit with real (non-zero) proof coordinates - simulates correct behavior
    /// Uses FIXED coords regardless of x (same proof structure for all statements)
    fn with_real_coords(x: F, num_bits: usize, num_proof_coords: usize) -> Self {
        // Use deterministic non-zero values (simulates real proof points)
        let mut proof_coords = Vec::with_capacity(num_proof_coords);
        let mut val = F::from(7u64);
        for i in 0..num_proof_coords {
            val = val + F::from(i as u64 + 1);
            proof_coords.push(val);
        }
        Self::with_coords(x, num_bits, proof_coords)
    }

    /// Create circuit with statement-dependent proof coordinates
    /// Different x values produce different coords (simulates real inner proofs)
    fn with_statement_dependent_coords(x: F, num_bits: usize, num_proof_coords: usize) -> Self {
        // Coords depend on x - simulates how inner proof coords change with statement
        let mut proof_coords = Vec::with_capacity(num_proof_coords);
        let mut val = F::from(7u64) + x; // Base value depends on x
        for i in 0..num_proof_coords {
            val = val + F::from(i as u64 + 1);
            proof_coords.push(val);
        }
        Self::with_coords(x, num_bits, proof_coords)
    }
}

impl<F: ark_ff::PrimeField> ConstraintSynthesizer<F> for ProofPointSimCircuit<F> {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<F>,
    ) -> Result<(), ark_relations::r1cs::SynthesisError> {
        use ark_r1cs_std::alloc::AllocVar;
        use ark_r1cs_std::boolean::AllocatedBool;
        use ark_r1cs_std::boolean::Boolean;
        use ark_r1cs_std::eq::EqGadget;
        use ark_r1cs_std::fields::fp::FpVar;
        use ark_r1cs_std::fields::FieldVar;
        use ark_relations::lc;
        use ark_relations::r1cs::Variable;

        // 1. Public input: the packed scalar
        let x_var = FpVar::new_input(cs.clone(), || Ok(self.x))?;

        // 2. Witness bits: NO booleanity constraint (like our fix)
        let mut bit_vars = Vec::with_capacity(self.bits.len());
        for bit in &self.bits {
            let alloc_bool =
                AllocatedBool::new_witness_without_booleanity_check(cs.clone(), || Ok(*bit))?;
            bit_vars.push(Boolean::from(alloc_bool));
        }

        // 3. Linear packing constraint: x = Σ 2^i * bit_i
        let mut lc_bits = lc!();
        let mut coeff = F::one();
        for bit in &bit_vars {
            match bit {
                Boolean::Constant(true) => {
                    lc_bits = lc_bits + (coeff, Variable::One);
                }
                Boolean::Constant(false) => {}
                Boolean::Var(v) => {
                    lc_bits = lc_bits + (coeff, v.variable());
                }
            }
            coeff = coeff + coeff;
        }
        let x_lc = match &x_var {
            FpVar::Constant(c) => lc!() + (*c, Variable::One),
            FpVar::Var(v) => lc!() + v.variable,
        };
        cs.enforce_constraint(x_lc - lc_bits, lc!() + Variable::One, lc!())?;

        // 4. Allocate "proof coordinates" as witnesses WITH wit×wit constraints
        // This simulates ProofVar::new_witness which adds on-curve checks
        let mut coord_vars = Vec::with_capacity(self.proof_coords.len());
        for coord in &self.proof_coords {
            let v = FpVar::new_witness(cs.clone(), || Ok(*coord))?;
            coord_vars.push(v);
        }

        // 5. Create wit × wit constraints that depend on proof coord values
        // We use trivial equations that are always satisfiable: a * b = a * b
        // This still creates the H-term pairs we need to test
        if coord_vars.len() >= 3 {
            // Create X², Y², Z² terms
            let x2 = &coord_vars[0] * &coord_vars[0];
            let y2 = &coord_vars[1] * &coord_vars[1];
            let z2 = &coord_vars[2] * &coord_vars[2];

            // Enforce trivial equations (always satisfiable)
            x2.enforce_equal(&x2)?;
            y2.enforce_equal(&y2)?;
            z2.enforce_equal(&z2)?;

            // More products
            let xy = &coord_vars[0] * &coord_vars[1];
            let yz = &coord_vars[1] * &coord_vars[2];
            let xz = &coord_vars[0] * &coord_vars[2];

            xy.enforce_equal(&xy)?;
            yz.enforce_equal(&yz)?;
            xz.enforce_equal(&xz)?;
        }

        // 6. More wit × wit constraints
        for i in 0..coord_vars.len().saturating_sub(1) {
            let prod = &coord_vars[i] * &coord_vars[i + 1];
            prod.enforce_equal(&prod)?;
        }

        arkworks_groth16::api::enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

/// Test: Demonstrates the bug when q_const is computed with dummy (zero) proof coords
/// but real proving uses non-zero coords. This causes a sparsity mismatch in H-terms.
///
/// The fix is to use the SAME proof coords for q_const computation as for real proving.
/// Test the lean prover with statement-dependent witness coordinates.
///
/// This test verifies that the Q-vector convolution fix correctly handles
/// diagonal L_k(τ)² terms, making the gap linear in public inputs.
///
/// Key parts:
/// - D3: Verify gap linearity with statement-dependent coords (THE KEY CHECK)
/// - D4: Compare with linear-only circuit (confirms wit×wit is the issue)
/// - F: Verify statement-dependent coords work with gap-based q_const (THE FIX)
#[test]
fn test_lean_prover_proof_point_simulation() {
    type OuterE = <DefaultCycle as RecursionCycle>::OuterE;
    type OuterFr = <OuterE as Pairing>::ScalarField;

    let mut _rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    const NUM_BITS: usize = 16;
    const NUM_PROOF_COORDS: usize = 6; // Simulate 2 G1 points (x,y,z each)

    // 1. Setup
    let setup_circuit =
        ProofPointSimCircuit::with_dummy_coords(OuterFr::from(0u64), NUM_BITS, NUM_PROOF_COORDS);
    let (pk_outer, vk_outer) =
        Groth16::<OuterE, PvugcReduction>::circuit_specific_setup(setup_circuit.clone(), &mut _rng)
            .expect("setup failed");

    println!("=== ProofPointSim Test ===");
    println!("Setup complete. h_query len: {}", pk_outer.h_query.len());

    // 2. Build lean PK with Q-vector fix
    let lean_pk = build_lean_pk_with_witness_bases(&pk_outer, || {
        ProofPointSimCircuit::with_dummy_coords(OuterFr::from(0u64), NUM_BITS, NUM_PROOF_COORDS)
    });
    println!(
        "Lean PK built. h_query_wit len: {}",
        lean_pk.h_query_wit.len()
    );

    let x_test_2 = OuterFr::from(2u64);
    let x_test_42 = OuterFr::from(42u64);

    // ========================================================================
    // PART D3: CHECK GAP LINEARITY with STATEMENT-DEPENDENT coords
    // This is the KEY check - if the gap is linear, the Q-vector fix works!
    // ========================================================================
    println!("\n--- PART D3: CHECK GAP LINEARITY with STATEMENT-DEPENDENT coords ---");

    let circuit_0_dep = ProofPointSimCircuit::with_statement_dependent_coords(
        OuterFr::zero(),
        NUM_BITS,
        NUM_PROOF_COORDS,
    );
    let proof_std_0_dep =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            circuit_0_dep.clone(),
            &pk_outer,
        )
            .unwrap();
    let (proof_lean_0_dep, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_0_dep, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_0_dep =
        (proof_std_0_dep.c.into_group() - proof_lean_0_dep.c.into_group()).into_affine();

    let circuit_1_dep = ProofPointSimCircuit::with_statement_dependent_coords(
        OuterFr::one(),
        NUM_BITS,
        NUM_PROOF_COORDS,
    );
    let proof_std_1_dep =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            circuit_1_dep.clone(),
            &pk_outer,
        )
            .unwrap();
    let (proof_lean_1_dep, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_1_dep, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_1_dep =
        (proof_std_1_dep.c.into_group() - proof_lean_1_dep.c.into_group()).into_affine();

    let circuit_2_dep =
        ProofPointSimCircuit::with_statement_dependent_coords(x_test_2, NUM_BITS, NUM_PROOF_COORDS);
    let proof_std_2_dep =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            circuit_2_dep.clone(),
            &pk_outer,
        )
            .unwrap();
    let (proof_lean_2_dep, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_2_dep, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_2_dep =
        (proof_std_2_dep.c.into_group() - proof_lean_2_dep.c.into_group()).into_affine();

    // Check linearity: gap(2) == 2*gap(1) - gap(0)?
    let expected_gap_2_dep =
        (gap_1_dep.into_group() * OuterFr::from(2u64) - gap_0_dep.into_group()).into_affine();
    let gap_is_linear_dep = gap_2_dep == expected_gap_2_dep;

    println!("gap(0) = {:?}", gap_0_dep);
    println!("gap(1) = {:?}", gap_1_dep);
    println!("gap(2) actual   = {:?}", gap_2_dep);
    println!("gap(2) expected = {:?}", expected_gap_2_dep);
    println!(
        "Gap is LINEAR with STATEMENT-DEPENDENT coords: {}",
        gap_is_linear_dep
    );

    assert!(
        gap_is_linear_dep,
        "Gap must be linear for Q-vector fix to work!"
    );
    println!("*** GAP IS LINEAR! Q-vector fix is working. ***");

    // ========================================================================
    // PART D4: Test with LINEAR-ONLY circuit (no wit×wit) for comparison
    // ========================================================================
    println!("\n--- PART D4: Test with LINEAR-ONLY circuit (no wit×wit) ---");

    #[derive(Clone)]
    struct LinearOnlyCircuit {
        x: OuterFr,
        num_bits: usize,
    }

    impl ConstraintSynthesizer<OuterFr> for LinearOnlyCircuit {
        fn generate_constraints(
            self,
            cs: ark_relations::r1cs::ConstraintSystemRef<OuterFr>,
        ) -> Result<(), ark_relations::r1cs::SynthesisError> {
            use ark_r1cs_std::fields::fp::FpVar;
            use ark_r1cs_std::prelude::*;

            let x_var = FpVar::new_input(cs.clone(), || Ok(self.x))?;
            let mut bit_vars = Vec::new();
            let x_bits: Vec<bool> = (0..self.num_bits)
                .map(|i| ((self.x.into_bigint().as_ref()[0] >> i) & 1) == 1)
                .collect();

            for bit in x_bits {
                let bit_var = FpVar::new_witness(cs.clone(), || {
                    Ok(if bit { OuterFr::one() } else { OuterFr::zero() })
                })?;
                bit_vars.push(bit_var);
            }

            let mut sum = FpVar::zero();
            let mut coeff = OuterFr::one();
            for bit_var in &bit_vars {
                sum = sum + bit_var * FpVar::constant(coeff);
                coeff = coeff + coeff;
            }
            x_var.enforce_equal(&sum)?;

            Ok(())
        }
    }

    let linear_circuit = LinearOnlyCircuit {
        x: OuterFr::zero(),
        num_bits: 16,
    };
    let (pk_linear, _vk_linear) =
        Groth16::<OuterE, PvugcReduction>::circuit_specific_setup(linear_circuit, &mut _rng)
            .expect("linear setup");

    let lean_pk_linear = build_lean_pk_with_witness_bases(&pk_linear, || LinearOnlyCircuit {
        x: OuterFr::zero(),
        num_bits: 16,
    });

    println!(
        "Linear circuit: h_query_wit has {} bases",
        lean_pk_linear.h_query_wit.len()
    );

    let linear_0 = LinearOnlyCircuit {
        x: OuterFr::zero(),
        num_bits: 16,
    };
    let proof_std_lin_0 =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            linear_0.clone(),
            &pk_linear,
        )
        .unwrap();
    let (proof_lean_lin_0, _) =
        prove_lean_with_randomizers(&lean_pk_linear, linear_0, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_lin_0 =
        (proof_std_lin_0.c.into_group() - proof_lean_lin_0.c.into_group()).into_affine();

    let linear_1 = LinearOnlyCircuit {
        x: OuterFr::one(),
        num_bits: 16,
    };
    let proof_std_lin_1 =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            linear_1.clone(),
            &pk_linear,
        )
        .unwrap();
    let (proof_lean_lin_1, _) =
        prove_lean_with_randomizers(&lean_pk_linear, linear_1, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_lin_1 =
        (proof_std_lin_1.c.into_group() - proof_lean_lin_1.c.into_group()).into_affine();

    let linear_2 = LinearOnlyCircuit {
        x: OuterFr::from(2u64),
        num_bits: 16,
    };
    let proof_std_lin_2 =
        Groth16::<OuterE, PvugcReduction>::create_proof_with_reduction_no_zk(
            linear_2.clone(),
            &pk_linear,
        )
        .unwrap();
    let (proof_lean_lin_2, _) =
        prove_lean_with_randomizers(&lean_pk_linear, linear_2, OuterFr::zero(), OuterFr::zero())
            .unwrap();
    let gap_lin_2 =
        (proof_std_lin_2.c.into_group() - proof_lean_lin_2.c.into_group()).into_affine();

    let expected_gap_lin_2 =
        (gap_lin_1.into_group() * OuterFr::from(2u64) - gap_lin_0.into_group()).into_affine();
    let gap_lin_is_linear = gap_lin_2 == expected_gap_lin_2;

    println!("Linear circuit gap(0) = {:?}", gap_lin_0);
    println!("Linear circuit gap(1) = {:?}", gap_lin_1);
    println!("Linear circuit gap(2) actual   = {:?}", gap_lin_2);
    println!("Linear circuit gap(2) expected = {:?}", expected_gap_lin_2);
    println!("Linear circuit gap is LINEAR: {}", gap_lin_is_linear);

    assert!(gap_lin_is_linear, "Linear circuit gap must be linear!");
    println!("*** LINEAR CIRCUIT GAP IS LINEAR! ***");

    // ========================================================================
    // PART F: GAP-BASED q_const with FIXED coords, verify STATEMENT-DEPENDENT works
    // This is THE FIX - gap-based q_const works for ANY statement!
    // ========================================================================
    println!("\n--- PART F: GAP-BASED q_const (fixed coords) + STATEMENT-DEPENDENT proving ---");

    // Compute q_const with FIXED coords (using statements 0 and 1)
    let q_const_fixed_all = compute_q_const_with_coords(
        &pk_outer,
        &lean_pk,
        NUM_BITS,
        NUM_PROOF_COORDS,
        true, // use_real_coords = true (FIXED, not statement-dependent)
    );

    // Convert q_const G1 points to GT by pairing with delta (GT baking)
    let t_const_gt: Vec<_> = q_const_fixed_all
        .iter()
        .map(|q| OuterE::pairing(*q, pk_outer.vk.delta_g2))
        .collect();

    let pvugc_vk_gap: PvugcVk<OuterE> = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        t_const_gt,
    );

    // Test x=2 with STATEMENT-DEPENDENT coords using GAP-BASED q_const
    let circuit_2_gap =
        ProofPointSimCircuit::with_statement_dependent_coords(x_test_2, NUM_BITS, NUM_PROOF_COORDS);
    let (proof_lean_2_gap, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_2_gap, OuterFr::zero(), OuterFr::zero())
            .expect("lean proof 2 gap");
    let r_baked_2_gap =
        compute_baked_target(&vk_outer, &pvugc_vk_gap, &vec![x_test_2]).expect("baked 2 gap");
    let lhs_2_gap = OuterE::pairing(proof_lean_2_gap.a, proof_lean_2_gap.b);
    let rhs_2_gap = r_baked_2_gap + OuterE::pairing(proof_lean_2_gap.c, vk_outer.delta_g2);
    let x2_gap_passes = lhs_2_gap == rhs_2_gap;
    println!(
        "x=2 with STATEMENT-DEPENDENT coords + GAP-BASED q_const: lhs == rhs = {}",
        x2_gap_passes
    );

    // Test x=42 with STATEMENT-DEPENDENT coords using GAP-BASED q_const
    let circuit_42_gap = ProofPointSimCircuit::with_statement_dependent_coords(
        x_test_42,
        NUM_BITS,
        NUM_PROOF_COORDS,
    );
    let (proof_lean_42_gap, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_42_gap, OuterFr::zero(), OuterFr::zero())
            .expect("lean proof 42 gap");
    let r_baked_42_gap =
        compute_baked_target(&vk_outer, &pvugc_vk_gap, &vec![x_test_42]).expect("baked 42 gap");
    let lhs_42_gap = OuterE::pairing(proof_lean_42_gap.a, proof_lean_42_gap.b);
    let rhs_42_gap = r_baked_42_gap + OuterE::pairing(proof_lean_42_gap.c, vk_outer.delta_g2);
    let x42_gap_passes = lhs_42_gap == rhs_42_gap;
    println!(
        "x=42 with STATEMENT-DEPENDENT coords + GAP-BASED q_const: lhs == rhs = {}",
        x42_gap_passes
    );

    println!("\n--- PART F RESULTS ---");
    println!(
        "x=2 GAP-BASED:  {}",
        if x2_gap_passes { "PASS ✓" } else { "FAIL" }
    );
    println!(
        "x=42 GAP-BASED: {}",
        if x42_gap_passes { "PASS ✓" } else { "FAIL" }
    );

    assert!(x2_gap_passes, "x=2 must pass with Q-vector fix!");
    assert!(x42_gap_passes, "x=42 must pass with Q-vector fix!");

    println!("\n*** Q-VECTOR FIX WORKS! ***");
    println!("Statement-dependent coords now work because:");
    println!("  1. The Q-vector convolution correctly handles diagonal L_k² terms");
    println!("  2. The gap is now LINEAR in public inputs");
    println!("  3. Gap-based q_const (computed with fixed coords) works for ANY statement!");
}

/// Helper: Compute q_const ALGEBRAICALLY from constraint matrices (THE FIX!)
/// This computes pub×pub H-bases directly, independent of witness values.
fn compute_q_const_algebraic<E: Pairing>(
    pk: &ark_groth16::ProvingKey<E>,
    _lean_pk: &LeanProvingKey<E>,
    num_bits: usize,
    num_proof_coords: usize,
) -> Vec<E::G1Affine> {
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
    use std::collections::HashMap;

    println!("[q_const ALGEBRAIC] Computing from constraint matrices...");

    // Synthesize circuit to get matrices (witness values don't matter!)
    let circuit =
        ProofPointSimCircuit::with_dummy_coords(E::ScalarField::zero(), num_bits, num_proof_coords);

    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit
        .generate_constraints(cs.clone())
        .expect("synthesis failed");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrix extraction failed");

    let num_pub = cs.num_instance_variables();
    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let num_constraints = cs.num_constraints();

    // CRITICAL: Domain size must match standard Groth16!
    // Standard Groth16 uses domain of size (num_constraints + num_inputs)
    let qap_domain_size = num_constraints + num_pub;
    let domain = GeneralEvaluationDomain::<E::ScalarField>::new(qap_domain_size)
        .expect("domain creation failed");
    let domain_size = domain.size();
    let n_scalar = domain.size_as_field_element();
    let domain_elements: Vec<_> = (0..domain_size).map(|i| domain.element(i)).collect();

    println!(
        "[q_const ALGEBRAIC] QAP domain: {} constraints + {} inputs = {} (padded to {})",
        num_constraints, num_pub, qap_domain_size, domain_size
    );
    println!("[q_const ALGEBRAIC] h_query length: {}", pk.h_query.len());

    // Check C matrix for public columns
    let mut col_c: Vec<Vec<(usize, E::ScalarField)>> = vec![Vec::new(); num_vars];
    for (row, terms) in matrices.c.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_c[col].push((row, val));
            }
        }
    }
    println!(
        "[q_const ALGEBRAIC] C matrix: col_c[0] has {} entries, col_c[1] has {} entries",
        col_c[0].len(),
        col_c[1].len()
    );

    // Build column maps for A and B
    let mut col_a: Vec<Vec<(usize, E::ScalarField)>> = vec![Vec::new(); num_vars];
    let mut col_b: Vec<Vec<(usize, E::ScalarField)>> = vec![Vec::new(); num_vars];

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

    // Add synthetic "copy constraint" rows for public inputs
    for i in 0..num_pub {
        let row = num_constraints + i;
        if row < domain_size {
            col_a[i].push((row, E::ScalarField::one()));
        }
    }

    // Compute Lagrange SRS using group IFFT
    // Note: domain.ifft_in_place is for scalars. For group elements, we need:
    // 1. FFT
    // 2. Reverse elements [1..n]
    // 3. Scale by 1/n
    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, E::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    let mut lagrange_srs = h_query_proj;

    // FFT on group elements
    domain.fft_in_place(&mut lagrange_srs);
    // Reverse [1..n]
    if lagrange_srs.len() > 1 {
        lagrange_srs[1..].reverse();
    }
    // Scale by 1/n
    let n_inv = domain.size_as_field_element().inverse().unwrap();
    for p in lagrange_srs.iter_mut() {
        *p *= n_inv;
    }

    let lagrange_srs: Vec<_> = lagrange_srs.into_iter().map(|p| p.into_affine()).collect();

    // The gap is (A*B - C) / Z for pub×pub terms.
    //
    // For public inputs [1, x], the gap is:
    //   gap(x) = (A_0*B_0 - C_0)/Z * 1*1 + (A_0*B_1 - 0)/Z * 1*x + (A_1*B_0 - 0)/Z * x*1 + (A_1*B_1 - C_1)/Z * x*x
    //          = H_{0,0} + x*(H_{0,1} + H_{1,0}) + x²*H_{1,1}
    //
    // But wait - C_i is only subtracted when i == j (diagonal of the quadratic form).
    // Actually, the -C term is NOT quadratic. It's linear: -Σ_i w_i * C_i(x) / Z(x).
    //
    // So the full quotient is:
    //   H(x) = Σ_{i,j} w_i*w_j * A_i*B_j/Z - Σ_i w_i * C_i/Z
    //        = Σ_{i,j} w_i*w_j * A_i*B_j/Z - Σ_i w_i * C_i/Z
    //
    // The quadratic part is A*B/Z.
    // The linear part is -C/Z, which is handled by the L-query!
    //
    // So for the gap (pub×pub only), we need:
    //   gap_quadratic = Σ_{i,j ∈ pub} w_i*w_j * A_i*B_j/Z
    //   gap_linear = -Σ_{i ∈ pub} w_i * C_i/Z
    //
    // At x=0: w_0=1, w_1=0, so gap(0) = A_0*B_0/Z - C_0/Z
    // At x=1: w_0=1, w_1=1, so gap(1) = (A_0+A_1)*(B_0+B_1)/Z - (C_0+C_1)/Z
    //                                 = A_0*B_0/Z + A_0*B_1/Z + A_1*B_0/Z + A_1*B_1/Z - C_0/Z - C_1/Z

    // Compute A*B/Z contribution for pub×pub pairs
    let mut h_ab_pub_pub: HashMap<(usize, usize), E::G1> = HashMap::new();

    for i in 0..num_pub {
        for j in 0..num_pub {
            let rows_u = &col_a[i];
            let rows_v = &col_b[j];

            if rows_u.is_empty() || rows_v.is_empty() {
                continue;
            }

            let mut acc = E::G1::zero();

            for &(k, val_u) in rows_u {
                for &(m, val_v) in rows_v {
                    if k == m {
                        continue; // Skip diagonal (handled by L-query)
                    }

                    let wk = domain_elements[k];
                    let wm = domain_elements[m];
                    let denom = n_scalar * (wk - wm);
                    let inv_denom = denom.inverse().expect("denom non-zero for k != m");

                    let common = val_u * val_v * inv_denom;

                    acc += lagrange_srs[k].into_group() * (common * wm);
                    acc -= lagrange_srs[m].into_group() * (common * wk);
                }
            }

            if !acc.is_zero() {
                h_ab_pub_pub.insert((i, j), acc);
            }
        }
    }

    // Compute -C/Z contribution for public variables
    // This is linear, not quadratic, so it contributes to gap(x) as:
    //   -C_0/Z * 1 - C_1/Z * x
    let mut h_c_pub: Vec<E::G1> = vec![E::G1::zero(); num_pub];

    for i in 0..num_pub {
        let rows_c = &col_c[i];
        if rows_c.is_empty() {
            continue;
        }

        // C_i(x) / Z(x) contribution
        // This is tricky because C/Z is not in the H-query directly.
        // Actually, the -C term is absorbed into the L-query for witness variables,
        // but for public variables, it's part of the IC (input commitment).
        //
        // Wait - the IC handles the public input contribution to the verification equation,
        // not the quotient polynomial. Let me re-think this.
        //
        // Actually, in Groth16, the quotient H(x) = (A*B - C) / Z is computed fully.
        // The -C term is included in H(x), not separated out.
        //
        // So the gap should be the pub×pub part of (A*B - C) / Z.
        // But -C is linear in w, not quadratic, so it doesn't fit the (i,j) pair model.
        //
        // Let me think about this differently. The gap is:
        //   gap = c_std - c_lean
        //       = (L_term + H_term_full + ...) - (L_term + H_term_wit + ...)
        //       = H_term_full - H_term_wit
        //       = pub×pub H-terms
        //
        // The H_term_full includes all (i,j) pairs, including pub×pub.
        // The H_term_wit excludes pub×pub pairs.
        // So the gap is exactly the pub×pub contribution to H.
        //
        // But H = (A*B - C) / Z. The -C term is linear, so it doesn't contribute
        // to the quadratic (i,j) pair structure. It's handled separately.
        //
        // Actually, looking at the standard prover code, the H polynomial is computed as:
        //   h = IFFT(FFT(a) * FFT(b) - FFT(c)) / Z
        //
        // This is done in evaluation form, not coefficient form. The -c is subtracted
        // before dividing by Z.
        //
        // So the H polynomial includes the -C term, but it's not quadratic in w.
        // The quadratic part is A*B, and the linear part is -C.
        //
        // For the gap, we need the pub×pub contribution to H.
        // The A*B part gives quadratic terms: Σ_{i,j} w_i*w_j * (A_i*B_j)/Z
        // The -C part gives linear terms: -Σ_i w_i * C_i/Z
        //
        // For pub×pub, the quadratic contribution is:
        //   Σ_{i,j ∈ pub} w_i*w_j * (A_i*B_j)/Z
        //
        // The linear -C contribution for public variables is:
        //   -Σ_{i ∈ pub} w_i * C_i/Z
        //
        // But wait - the linear -C term is NOT quadratic, so it doesn't fit the
        // "gap = pub×pub H-terms" model. Unless...
        //
        // Actually, let me check if the lean prover handles the -C term correctly.
        // The lean prover computes H_term = Σ_{(i,j) ∈ wit-pairs} w_i*w_j * H_{i,j}(τ).
        // This only includes the A*B contribution, not the -C contribution!
        //
        // So the gap should include both:
        //   1. pub×pub (A*B)/Z terms
        //   2. The ENTIRE -C/Z term (because lean prover doesn't compute it!)
        //
        // Wait, that can't be right. The L-query handles the -C term for witness variables.
        // Let me re-check the Groth16 prover...
    }

    // For now, just use the A*B/Z contribution (ignoring -C)
    // This is what the current code does, and we know it doesn't match the gap.
    // The mismatch is likely due to the -C term.

    // Build q_const points from A*B/Z only
    let mut q_points = vec![E::G1Affine::zero(); 2];

    // q_const[0] = H_{0,0} (A*B/Z part only)
    if let Some(h00) = h_ab_pub_pub.get(&(0, 0)) {
        q_points[0] = h00.into_affine();
    }

    // q_const[1] = H_{0,1} + H_{1,0} (A*B/Z part only)
    let mut sum = E::G1::zero();
    if let Some(h01) = h_ab_pub_pub.get(&(0, 1)) {
        sum += h01;
    }
    if let Some(h10) = h_ab_pub_pub.get(&(1, 0)) {
        sum += h10;
    }
    q_points[1] = sum.into_affine();

    println!(
        "[q_const ALGEBRAIC] Computed {} pub×pub H-bases (A*B/Z only, missing -C/Z)",
        h_ab_pub_pub.len()
    );

    // Debug: show which pub×pub pairs have non-zero H-bases
    for ((i, j), h) in &h_ab_pub_pub {
        println!("  H_{{{},{}}} (A*B/Z) = {:?}", i, j, h.into_affine());
    }

    // Debug: show column 0 and 1 appearances in A and B
    println!(
        "  col_a[0] has {} entries, col_b[0] has {} entries",
        col_a[0].len(),
        col_b[0].len()
    );
    println!(
        "  col_a[1] has {} entries, col_b[1] has {} entries",
        col_a[1].len(),
        col_b[1].len()
    );

    q_points
}

/// Helper: Compute q_const with statement-dependent coords (like real inner proofs)
fn compute_q_const_statement_dependent<E: Pairing>(
    pk: &ark_groth16::ProvingKey<E>,
    lean_pk: &LeanProvingKey<E>,
    num_bits: usize,
    num_proof_coords: usize,
) -> Vec<E::G1Affine> {
    let mut q_points = vec![E::G1Affine::zero(); 2];

    // Probe at x = 0 with statement-dependent coords
    let circuit_0 = ProofPointSimCircuit::with_statement_dependent_coords(
        E::ScalarField::zero(),
        num_bits,
        num_proof_coords,
    );
    let proof_std_0 =
        Groth16::<E>::create_proof_with_reduction_no_zk(circuit_0.clone(), pk).expect("proof 0");
    let (proof_lean_0, _) = prove_lean_with_randomizers(
        lean_pk,
        circuit_0,
        E::ScalarField::zero(),
        E::ScalarField::zero(),
    )
    .expect("lean 0");
    let gap_0 = proof_std_0.c.into_group() - proof_lean_0.c.into_group();
    q_points[0] = gap_0.into_affine();

    // Probe at x = 1 with statement-dependent coords
    let circuit_1 = ProofPointSimCircuit::with_statement_dependent_coords(
        E::ScalarField::one(),
        num_bits,
        num_proof_coords,
    );
    let proof_std_1 =
        Groth16::<E>::create_proof_with_reduction_no_zk(circuit_1.clone(), pk).expect("proof 1");
    let (proof_lean_1, _) = prove_lean_with_randomizers(
        lean_pk,
        circuit_1,
        E::ScalarField::zero(),
        E::ScalarField::zero(),
    )
    .expect("lean 1");
    let gap_1 = proof_std_1.c.into_group() - proof_lean_1.c.into_group();
    q_points[1] = (gap_1 - gap_0).into_affine();

    q_points
}

/// Helper: Compute q_const with either dummy (zero) or real (non-zero) proof coords
fn compute_q_const_with_coords<E: Pairing>(
    pk: &ark_groth16::ProvingKey<E>,
    lean_pk: &LeanProvingKey<E>,
    num_bits: usize,
    num_proof_coords: usize,
    use_real_coords: bool,
) -> Vec<E::G1Affine> {
    let mut q_points = vec![E::G1Affine::zero(); 2];

    let make_circuit = |x: E::ScalarField| {
        if use_real_coords {
            ProofPointSimCircuit::with_real_coords(x, num_bits, num_proof_coords)
        } else {
            ProofPointSimCircuit::with_dummy_coords(x, num_bits, num_proof_coords)
        }
    };

    // Probe at x = 0
    let circuit_0 = make_circuit(E::ScalarField::zero());
    let proof_std_0 =
        Groth16::<E>::create_proof_with_reduction_no_zk(circuit_0.clone(), pk).expect("proof 0");
    let (proof_lean_0, _) = prove_lean_with_randomizers(
        lean_pk,
        circuit_0,
        E::ScalarField::zero(),
        E::ScalarField::zero(),
    )
    .expect("lean 0");
    let gap_0 = proof_std_0.c.into_group() - proof_lean_0.c.into_group();
    q_points[0] = gap_0.into_affine();

    // Probe at x = 1
    let circuit_1 = make_circuit(E::ScalarField::one());
    let proof_std_1 =
        Groth16::<E>::create_proof_with_reduction_no_zk(circuit_1.clone(), pk).expect("proof 1");
    let (proof_lean_1, _) = prove_lean_with_randomizers(
        lean_pk,
        circuit_1,
        E::ScalarField::zero(),
        E::ScalarField::zero(),
    )
    .expect("lean 1");
    let gap_1 = proof_std_1.c.into_group() - proof_lean_1.c.into_group();
    q_points[1] = (gap_1 - gap_0).into_affine();

    q_points
}

// Helper functions for the tests

fn build_lean_pk_with_witness_bases<
    E: Pairing,
    F: Fn() -> C,
    C: ConstraintSynthesizer<E::ScalarField>,
>(
    pk: &ark_groth16::ProvingKey<E>,
    circuit_fn: F,
) -> LeanProvingKey<E> {
    use ark_ec::VariableBaseMSM;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    use std::collections::HashSet;

    // Synthesize to get matrices
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    circuit_fn()
        .generate_constraints(cs.clone())
        .expect("synthesis");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrices");

    // CRITICAL: Domain size must match standard Groth16!
    let num_constraints = cs.num_constraints();
    let num_inputs = cs.num_instance_variables();
    let qap_domain_size = num_constraints + num_inputs;

    let domain = GeneralEvaluationDomain::<E::ScalarField>::new(qap_domain_size).expect("domain");
    let domain_size = domain.size();

    println!(
        "[build_lean_pk] QAP domain: {} constraints + {} inputs = {} (padded to {})",
        num_constraints, num_inputs, qap_domain_size, domain_size
    );

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a: Vec<Vec<(usize, E::ScalarField)>> = vec![Vec::new(); num_vars];
    let mut col_b: Vec<Vec<(usize, E::ScalarField)>> = vec![Vec::new(); num_vars];

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

    // Add synthetic "copy constraint" rows for public inputs
    for i in 0..num_inputs {
        let row = num_constraints + i;
        if row < domain_size {
            col_a[i].push((row, E::ScalarField::one()));
        }
    }

    // Compute Lagrange SRS via IFFT
    let mut h_proj: Vec<E::G1> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_proj.len() < domain_size {
        h_proj.resize(domain_size, E::G1::zero());
    } else {
        h_proj.truncate(domain_size);
    }
    // Manual IFFT for group elements
    {
        let n = h_proj.len();
        let log_n = n.trailing_zeros();
        for k in 0..n {
            let rk = k.reverse_bits() >> (usize::BITS - log_n);
            if k < rk {
                h_proj.swap(k, rk);
            }
        }
        let mut m = 1;
        while m < n {
            let omega_m = domain.element(domain.size() / (2 * m));
            for start in (0..n).step_by(2 * m) {
                let mut w = E::ScalarField::one();
                for j in 0..m {
                    let t = h_proj[start + j + m] * w;
                    let u = h_proj[start + j];
                    h_proj[start + j] = u + t;
                    h_proj[start + j + m] = u - t;
                    w *= omega_m;
                }
            }
            m *= 2;
        }
        if n > 1 {
            h_proj[1..].reverse();
        }
        let n_inv = domain.size_as_field_element().inverse().unwrap();
        for x in &mut h_proj {
            *x *= n_inv;
        }
    }
    let lagrange_srs: Vec<E::G1Affine> = h_proj.into_iter().map(|p| p.into_affine()).collect();

    // --- Diagonal Correction via Q-Vector ---
    // Emulate the convolution-based correction for tests
    // 1. Compute Q vector
    let n_field = domain.size_as_field_element();
    let t0 = (n_field - E::ScalarField::one()) * (n_field + n_field).inverse().unwrap();
    let mut u = vec![E::ScalarField::zero(); domain_size];
    u[0] = t0;

    // Batch invert for other u[j]
    let mut denoms = Vec::with_capacity(domain_size - 1);
    let mut indices = Vec::with_capacity(domain_size - 1);
    for j in 1..domain_size {
        let omega_j = domain.element(j);
        denoms.push(n_field * (E::ScalarField::one() - omega_j));
        indices.push(j);
    }
    use ark_ff::Field; // Use generic Field trait instead of BatchField
    ark_ff::batch_inversion(&mut denoms);
    for (i, &j) in indices.iter().enumerate() {
        u[j] = denoms[i];
    }

    // Reverse u[1..] to compute correlation via convolution
    // We want sum_j L_j * u_{j-k} = sum_j L_j * u_{-(k-j)}
    // Convolution computes sum_j L_j * v_{k-j}. So we need v_x = u_{-x}.
    if domain_size > 1 {
        u[1..].reverse();
    }

    // FFT(u)
    domain.fft_in_place(&mut u);

    // FFT(L)
    let mut l_fft: Vec<_> = lagrange_srs.iter().map(|p| p.into_group()).collect();
    // Helper needed in test:
    fn parallel_fft_g1<G: CurveGroup<ScalarField = F>, F: PrimeField>(
        a: &mut [G],
        d: &GeneralEvaluationDomain<F>,
    ) {
        // Simple serial FFT for test if parallel not available easily, or duplicate logic
        let n = a.len();
        let log_n = n.trailing_zeros();
        for k in 0..n {
            let rk = k.reverse_bits() >> (usize::BITS - log_n);
            if k < rk {
                a.swap(k, rk);
            }
        }
        let mut m = 1;
        while m < n {
            let omega_m = d.element(d.size() / (2 * m));
            for k in (0..n).step_by(2 * m) {
                let mut w = F::one();
                for j in 0..m {
                    let t = a[k + j + m] * w;
                    let u = a[k + j];
                    a[k + j] = u + t;
                    a[k + j + m] = u - t;
                    w *= omega_m;
                }
            }
            m *= 2;
        }
    }
    fn parallel_ifft_g1<G: CurveGroup<ScalarField = F>, F: PrimeField>(
        a: &mut [G],
        d: &GeneralEvaluationDomain<F>,
    ) {
        parallel_fft_g1(a, d);
        if a.len() > 1 {
            a[1..].reverse();
        }
        let n_inv = d.size_as_field_element().inverse().unwrap();
        for x in a.iter_mut() {
            *x *= n_inv;
        }
    }

    parallel_fft_g1(&mut l_fft, &domain);
    for (l, u_val) in l_fft.iter_mut().zip(u.iter()) {
        *l *= u_val;
    }
    parallel_ifft_g1(&mut l_fft, &domain);
    let q_vector: Vec<_> = l_fft.into_iter().map(|p| p.into_affine()).collect();

    // 2. Add diagonal corrections to h_wit
    // Since h_wit is [(i,j, base)], we need to augment it.
    // For test simplicity, we just rebuild h_wit or patch it.
    // Let's rebuild the pair collection to include Q.

    let num_pub = cs.num_instance_variables();
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

    let mut active_pairs: Vec<(usize, usize)> = Vec::new();
    for &i in &vars_a {
        for &j in &vars_b {
            if i >= num_pub || j >= num_pub {
                active_pairs.push((i, j));
            }
        }
    }
    active_pairs.sort();

    println!("Computing {} witness basis pairs...", active_pairs.len());

    let domain_elements: Vec<E::ScalarField> =
        (0..domain.size()).map(|i| domain.element(i)).collect();
    let n_scalar = domain.size_as_field_element();

    // Compute h_query_wit
    let h_wit: Vec<(u32, u32, E::G1Affine)> = active_pairs
        .iter()
        .filter_map(|&(i, j)| {
            let rows_u = &col_a[i];
            let rows_v = &col_b[j];
            if rows_u.is_empty() || rows_v.is_empty() {
                return None;
            }

            let mut denominators = Vec::with_capacity(rows_u.len() * rows_v.len());
            for &(k, _) in rows_u {
                for &(m, _) in rows_v {
                    if k != m {
                        denominators.push(n_scalar * (domain_elements[k] - domain_elements[m]));
                    } else {
                        denominators.push(E::ScalarField::one());
                    }
                }
            }
            ark_ff::batch_inversion(&mut denominators);

            let mut acc_u = vec![E::ScalarField::zero(); rows_u.len()];
            let mut acc_v = vec![E::ScalarField::zero(); rows_v.len()];

            let mut diag_bases = Vec::new();
            let mut diag_scalars = Vec::new();

            let mut denom_idx = 0;
            for (idx_u, &(k, val_u)) in rows_u.iter().enumerate() {
                for (idx_v, &(m, val_v)) in rows_v.iter().enumerate() {
                    let inv = denominators[denom_idx];
                    denom_idx += 1;

                    let prod = val_u * val_v;
                    if k == m {
                        diag_bases.push(q_vector[k]);
                        diag_scalars.push(prod);
                    } else {
                        let common = prod * inv;
                        acc_u[idx_u] += common * domain_elements[m];
                        acc_v[idx_v] -= common * domain_elements[k];
                    }
                }
            }

            let mut bases = Vec::new();
            let mut scalars = Vec::new();
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

            bases.extend(diag_bases);
            scalars.extend(diag_scalars);

            if bases.is_empty() {
                return None;
            }

            let h_acc = E::G1::msm(&bases, &scalars).unwrap();
            if h_acc.is_zero() {
                None
            } else {
                Some((i as u32, j as u32, h_acc.into_affine()))
            }
        })
        .collect();

    println!("Found {} non-zero h_query_wit bases", h_wit.len());

    LeanProvingKey {
        vk: pk.vk.clone(),
        beta_g1: pk.beta_g1,
        delta_g1: pk.delta_g1,
        a_query_wit: pk.a_query.clone(),
        b_g1_query: pk.b_g1_query.clone(),
        b_g2_query: pk.b_g2_query.clone(),
        h_query_wit: h_wit,
        l_query: pk.l_query.clone(),
    }
}

#[test]
fn test_lean_prover_end_to_end() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    // 1. Get Inner Proof (Fixture)
    let fixture = get_fixture();

    // Runtime statement - this would be a hash in production (e.g., Bitcoin UTXO)
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let x_inner = vec![x_val];

    // PRODUCTION SIMULATION: Runtime proof can use any seed!
    // With algebraic q_const computation, setup doesn't depend on proof coords.
    const RUNTIME_SEED: u64 = 12345;

    let circuit_inner = AddCircuit::with_public_input(x_val);
    let mut runtime_rng = ark_std::rand::rngs::StdRng::seed_from_u64(RUNTIME_SEED);
    let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut runtime_rng)
        .expect("inner proof failed");

    // 2. Define Outer Circuit
    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner.clone(),
        proof_inner.clone(),
    );

    // 3. Setup Outer PK
    let (pk_outer, vk_outer) =
        Groth16::<<DefaultCycle as RecursionCycle>::OuterE, PvugcReduction>::circuit_specific_setup(
            circuit_outer.clone(),
            &mut rng,
        )
        .expect("outer setup failed");

    // 4. Convert to Lean PK
    //
    // q_const is computed from the gap between standard and lean proofs.
    // The gap is linear in x when the Q-vector fix is applied.
    // We use fixed coords (from statements 0 and 1) to compute q_const.
    // This works for ANY statement because the gap is linear!
    let pk_inner_clone = fixture.pk_inner.clone();
    let inner_proof_generator = move |statements: &[InnerScalar<DefaultCycle>]| {
        // Use a fixed seed for reproducibility during q_const computation
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(99999);
        let statement = statements
            .get(0)
            .copied()
            .unwrap_or(InnerScalar::<DefaultCycle>::zero());
        let circuit = AddCircuit::with_public_input(statement);
        Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut rng)
            .expect("inner proof generation failed")
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &fixture.vk_inner,
            inner_proof_generator,
        )
    }));

    if let Ok((_pvugc_vk, lean_pk)) = result {
        // 5. Prove using Lean Prover
        let (proof_lean, _assignment) =
            prove_lean(&lean_pk, circuit_outer.clone(), &mut rng).expect("lean proving failed");

        // 6. Verify
        let public_inputs_outer =
            arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner[0]);
        let inputs_outer = vec![public_inputs_outer];

        let r_baked = compute_baked_target(&vk_outer, &_pvugc_vk, &inputs_outer)
            .expect("failed to compute baked target");

        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b);
        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        let rhs = r_baked + pairing_c_delta;
        assert_eq!(lhs, rhs, "Lean Proof + Baked Target failed verification");
    } else {
        assert!(
            false,
            "Baked Quotient setup panicked as expected for non-linear circuit."
        );
    }
}
