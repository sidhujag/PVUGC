//! Test for Lean Prover implementation
//!
//! Verifies that the "Lean Prover" (using sparse H-bases) produces valid Groth16 proofs
//! that are accepted by the standard Verifier.

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
use ark_std::{rand::SeedableRng, Zero};
use arkworks_groth16::outer_compressed::{
    OuterCircuit, InnerScalar, DefaultCycle, InnerE, OuterScalar,
};
use arkworks_groth16::test_fixtures::get_fixture;
use arkworks_groth16::test_circuits::AddCircuit;
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
use arkworks_groth16::prover_lean::{prove_lean, prove_lean_with_randomizers, LeanProvingKey};
use arkworks_groth16::ppe::{compute_baked_target, PvugcVk};
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
    pub x: F,                    // Public input (packed scalar)
    pub proof_coords: Vec<F>,    // Simulated proof point coordinates (passed in, not generated)
    pub bits: Vec<bool>,         // Bits for packing constraint
}

impl<F: ark_ff::PrimeField> ProofPointSimCircuit<F> {
    /// Create circuit with specific proof coordinates (for testing dummy vs real)
    fn with_coords(x: F, num_bits: usize, proof_coords: Vec<F>) -> Self {
        use ark_ff::BigInteger;
        
        // Bits are derived from x (like in real OuterCircuit)
        let mut bits = x.into_bigint().to_bits_le();
        bits.truncate(num_bits);
        bits.resize(num_bits, false);
        
        Self { x, proof_coords, bits }
    }
    
    /// Create circuit with dummy (zero) proof coordinates - simulates old buggy behavior
    fn with_dummy_coords(x: F, num_bits: usize, num_proof_coords: usize) -> Self {
        let proof_coords = vec![F::zero(); num_proof_coords];
        Self::with_coords(x, num_bits, proof_coords)
    }
    
    /// Create circuit with real (non-zero) proof coordinates - simulates correct behavior
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
}

impl<F: ark_ff::PrimeField> ConstraintSynthesizer<F> for ProofPointSimCircuit<F> {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<F>,
    ) -> Result<(), ark_relations::r1cs::SynthesisError> {
        use ark_r1cs_std::alloc::AllocVar;
        use ark_r1cs_std::boolean::AllocatedBool;
        use ark_r1cs_std::boolean::Boolean;
        use ark_r1cs_std::fields::fp::FpVar;
        use ark_r1cs_std::eq::EqGadget;
        use ark_r1cs_std::fields::FieldVar;
        use ark_relations::lc;
        use ark_relations::r1cs::Variable;

        // 1. Public input: the packed scalar
        let x_var = FpVar::new_input(cs.clone(), || Ok(self.x))?;

        // 2. Witness bits: NO booleanity constraint (like our fix)
        let mut bit_vars = Vec::with_capacity(self.bits.len());
        for bit in &self.bits {
            let alloc_bool = AllocatedBool::new_witness_without_booleanity_check(
                cs.clone(),
                || Ok(*bit),
            )?;
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

        // 4. Allocate "proof coordinates" as witnesses
        let mut coord_vars = Vec::with_capacity(self.proof_coords.len());
        for coord in &self.proof_coords {
            let v = FpVar::new_witness(cs.clone(), || Ok(*coord))?;
            coord_vars.push(v);
        }

        // 5. Simulate on-curve check: witness × witness constraints
        // Real on-curve check: Y² * Z = X³ + aX * Z² + bZ³
        // Simplified: just do some multiplications between proof coords
        if coord_vars.len() >= 3 {
            // Simulate X², Y², Z²
            let x2 = &coord_vars[0] * &coord_vars[0];
            let y2 = &coord_vars[1] * &coord_vars[1];
            let z2 = &coord_vars[2] * &coord_vars[2];
            
            // Simulate X³ = X * X²
            let x3 = &coord_vars[0] * &x2;
            
            // Simulate Y² * Z
            let y2z = &y2 * &coord_vars[2];
            
            // Just enforce these equal themselves (trivial but creates constraints)
            x3.enforce_equal(&x3)?;
            y2z.enforce_equal(&y2z)?;
            z2.enforce_equal(&z2)?;
        }

        // 6. Simulate more witness × witness (like scalar multiplication in subgroup check)
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
#[test]
fn test_lean_prover_proof_point_simulation() {
    type OuterE = <DefaultCycle as RecursionCycle>::OuterE;
    type OuterFr = <OuterE as Pairing>::ScalarField;

    let mut _rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

    const NUM_BITS: usize = 16;
    const NUM_PROOF_COORDS: usize = 6; // Simulate 2 G1 points (x,y,z each)

    // 1. Setup with dummy coords (this is fine - just defines circuit structure)
    let setup_circuit = ProofPointSimCircuit::with_dummy_coords(OuterFr::from(0u64), NUM_BITS, NUM_PROOF_COORDS);
    let (pk_outer, vk_outer) =
        Groth16::<OuterE>::circuit_specific_setup(setup_circuit.clone(), &mut _rng)
            .expect("setup failed");

    println!("=== ProofPointSim Test ===");
    println!("Setup complete. h_query len: {}", pk_outer.h_query.len());

    // 2. Build lean PK (this uses circuit structure, coords don't matter here)
    let lean_pk = build_lean_pk_with_witness_bases(&pk_outer, || {
        ProofPointSimCircuit::with_dummy_coords(OuterFr::from(0u64), NUM_BITS, NUM_PROOF_COORDS)
    });
    println!("Lean PK built. h_query_wit len: {}", lean_pk.h_query_wit.len());

    // ========================================================================
    // PART A: Demonstrate the BUG - q_const with dummy, proving with real
    // ========================================================================
    println!("\n--- PART A: BUG DEMONSTRATION (dummy q_const, real proving) ---");
    
    // Compute q_const with DUMMY (zero) coords - THIS IS THE BUG
    let q_const_buggy = compute_q_const_with_coords(
        &pk_outer,
        &lean_pk,
        NUM_BITS,
        NUM_PROOF_COORDS,
        false, // use_real_coords = false (dummy zeros)
    );
    
    let pvugc_vk_buggy: PvugcVk<OuterE> = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        q_const_buggy,
    );

    // Now prove with REAL (non-zero) coords
    let x_val = OuterFr::from(42u64);
    let circuit_real = ProofPointSimCircuit::with_real_coords(x_val, NUM_BITS, NUM_PROOF_COORDS);

    let proof_std = Groth16::<OuterE>::create_proof_with_reduction_no_zk(circuit_real.clone(), &pk_outer)
        .expect("standard proof failed");
    let (proof_lean, _) =
        prove_lean_with_randomizers(&lean_pk, circuit_real.clone(), OuterFr::zero(), OuterFr::zero())
            .expect("lean proof failed");

    // Check if it verifies (it should FAIL!)
    let inputs_outer = vec![x_val];
    let r_baked_buggy =
        compute_baked_target(&vk_outer, &pvugc_vk_buggy, &inputs_outer).expect("baked target failed");

    let lhs = OuterE::pairing(proof_lean.a, proof_lean.b);
    let pairing_c_delta = OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
    let rhs_buggy = r_baked_buggy + pairing_c_delta;

    let buggy_verifies = lhs == rhs_buggy;
    println!("Buggy setup (dummy q_const, real proof): lhs == rhs = {}", buggy_verifies);
    
    // The bug: c_gap != q_eval because sparsity patterns differ
    let c_gap = (proof_std.c.into_group() - proof_lean.c.into_group()).into_affine();
    let mut q_sum_buggy = pvugc_vk_buggy.q_const_points[0].into_group();
    q_sum_buggy += pvugc_vk_buggy.q_const_points[1] * x_val;
    let q_eval_buggy = q_sum_buggy.into_affine();
    println!("c_gap == q_eval (buggy): {}", c_gap == q_eval_buggy);

    // ========================================================================
    // PART B: Demonstrate the FIX - q_const with real coords, proving with real
    // ========================================================================
    println!("\n--- PART B: FIX DEMONSTRATION (real q_const, real proving) ---");
    
    // Compute q_const with REAL (non-zero) coords - THIS IS THE FIX
    let q_const_fixed = compute_q_const_with_coords(
        &pk_outer,
        &lean_pk,
        NUM_BITS,
        NUM_PROOF_COORDS,
        true, // use_real_coords = true
    );
    
    let pvugc_vk_fixed: PvugcVk<OuterE> = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        q_const_fixed,
    );

    // Verify with fixed q_const
    let r_baked_fixed =
        compute_baked_target(&vk_outer, &pvugc_vk_fixed, &inputs_outer).expect("baked target failed");
    let rhs_fixed = r_baked_fixed + pairing_c_delta;

    let fixed_verifies = lhs == rhs_fixed;
    println!("Fixed setup (real q_const, real proof): lhs == rhs = {}", fixed_verifies);

    let mut q_sum_fixed = pvugc_vk_fixed.q_const_points[0].into_group();
    q_sum_fixed += pvugc_vk_fixed.q_const_points[1] * x_val;
    let q_eval_fixed = q_sum_fixed.into_affine();
    println!("c_gap == q_eval (fixed): {}", c_gap == q_eval_fixed);

    // ========================================================================
    // ASSERTIONS
    // ========================================================================
    println!("\n--- ASSERTIONS ---");
    
    // The buggy version should FAIL (this demonstrates the bug exists)
    assert!(!buggy_verifies, "BUG DEMO: Buggy setup should NOT verify (proves the bug exists)");
    assert_ne!(c_gap, q_eval_buggy, "BUG DEMO: c_gap should NOT equal q_eval with dummy coords");
    
    // The fixed version should PASS
    assert!(fixed_verifies, "FIX: Fixed setup should verify");
    assert_eq!(c_gap, q_eval_fixed, "FIX: c_gap should equal q_eval with real coords");

    println!("\nSUCCESS: Demonstrated bug with dummy coords and fix with real coords!");
    println!("  - Buggy (dummy coords): verification FAILED as expected");
    println!("  - Fixed (real coords):  verification PASSED");
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
    let (proof_lean_0, _) =
        prove_lean_with_randomizers(lean_pk, circuit_0, E::ScalarField::zero(), E::ScalarField::zero())
            .expect("lean 0");
    let gap_0 = proof_std_0.c.into_group() - proof_lean_0.c.into_group();
    q_points[0] = gap_0.into_affine();

    // Probe at x = 1
    let circuit_1 = make_circuit(E::ScalarField::one());
    let proof_std_1 =
        Groth16::<E>::create_proof_with_reduction_no_zk(circuit_1.clone(), pk).expect("proof 1");
    let (proof_lean_1, _) =
        prove_lean_with_randomizers(lean_pk, circuit_1, E::ScalarField::zero(), E::ScalarField::zero())
            .expect("lean 1");
    let gap_1 = proof_std_1.c.into_group() - proof_lean_1.c.into_group();
    q_points[1] = (gap_1 - gap_0).into_affine();

    q_points
}

// Helper functions for the tests

fn build_lean_pk_with_witness_bases<E: Pairing, F: Fn() -> C, C: ConstraintSynthesizer<E::ScalarField>>(
    pk: &ark_groth16::ProvingKey<E>,
    circuit_fn: F,
) -> LeanProvingKey<E> {
    use ark_ec::VariableBaseMSM;
    use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
    use std::collections::HashSet;

    // Synthesize to get matrices
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    circuit_fn().generate_constraints(cs.clone()).expect("synthesis");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrices");

    let domain = GeneralEvaluationDomain::<E::ScalarField>::new(cs.num_constraints())
        .expect("domain");
    let domain_size = domain.size();

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
                    if k == m {
                        denominators.push(E::ScalarField::one());
                    } else {
                        denominators.push(n_scalar * (domain_elements[k] - domain_elements[m]));
                    }
                }
            }
            ark_ff::batch_inversion(&mut denominators);

            let mut acc_u = vec![E::ScalarField::zero(); rows_u.len()];
            let mut acc_v = vec![E::ScalarField::zero(); rows_v.len()];

            let mut denom_idx = 0;
            for (idx_u, &(k, val_u)) in rows_u.iter().enumerate() {
                for (idx_v, &(m, val_v)) in rows_v.iter().enumerate() {
                    let inv = denominators[denom_idx];
                    denom_idx += 1;
                    if k == m {
                        continue;
                    }
                    let common = val_u * val_v * inv;
                    acc_u[idx_u] += common * domain_elements[m];
                    acc_v[idx_v] -= common * domain_elements[k];
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
        a_query: pk.a_query.clone(),
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
    // Create a valid inner proof for the AddCircuit with public input x=10
    let x_val = InnerScalar::<DefaultCycle>::from(10u64); 
    let x_1val = InnerScalar::<DefaultCycle>::from(100u64); 

    let circuit_inner = AddCircuit::with_public_input(x_1val);
    let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng)
        .expect("inner proof failed");
    let x_inner = vec![x_val];

    // 2. Define Outer Circuit
    let circuit_outer = OuterCircuit::<DefaultCycle>::new(
        (*fixture.vk_inner).clone(),
        x_inner.clone(),
        proof_inner.clone()  // Clone so we can reuse for setup
    );

    // 3. Setup Outer PK
    let (pk_outer, vk_outer) = Groth16::< <DefaultCycle as RecursionCycle>::OuterE >::circuit_specific_setup(
        circuit_outer.clone(),
        &mut rng
    ).expect("outer setup failed");

    // 4. Convert to Lean PK
    // We need to pass a valid inner proof for q_const computation to ensure
    // the witness sparsity pattern matches real proofs.
    // We can reuse proof_inner - any valid proof works, the statement doesn't matter.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        build_pvugc_setup_from_pk_for::<DefaultCycle>(&pk_outer, &fixture.vk_inner, &proof_inner)
    }));

    if let Ok((_pvugc_vk, lean_pk)) = result {
        // 5. Prove using Lean Prover
        let (proof_lean, _assignment) = prove_lean(
            &lean_pk,
            circuit_outer.clone(),
            &mut rng
        ).expect("lean proving failed");

        // 6. Verify
        let public_inputs_outer =
            arkworks_groth16::outer_compressed::fr_inner_to_outer(&x_inner[0]);
        let inputs_outer = vec![public_inputs_outer];


        let r_baked = compute_baked_target(
            &vk_outer,
            &_pvugc_vk,
            &inputs_outer
        ).expect("failed to compute baked target");
        
        let lhs = <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.a, proof_lean.b);
        let pairing_c_delta =
            <DefaultCycle as RecursionCycle>::OuterE::pairing(proof_lean.c, vk_outer.delta_g2);
        let rhs = r_baked + pairing_c_delta;
        assert_eq!(lhs, rhs, "Lean Proof + Baked Target failed verification");
    } else {
        assert!(false, "Baked Quotient setup panicked as expected for non-linear circuit.");
    }
}