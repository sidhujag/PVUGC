//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use crate::arming::{ColumnArms, ColumnBases};
use crate::outer_compressed::{
    fr_inner_to_outer_for, DefaultCycle, InnerFr, InnerScalar, OuterCircuit, OuterE, OuterFr,
    OuterScalar, RecursionCycle, InnerVk,
};
use crate::ppe::PvugcVk;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_groth16::{VerifyingKey as Groth16VK, ProvingKey as Groth16PK};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    DenseUVPolynomial,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::UniformRand;

/// Build PVUGC VK from the OUTER proving key (populates b_g2_query)
///
/// These right-legs are constant size for the small outer verifier circuit.
///
/// SECURITY NOTE: For production, the `pk_outer` provided here MUST be a "Lean Proving Key"
/// (stripped of raw Powers of Tau) to prevent "Full Span" algebraic attacks.
/// Standard `ark_groth16::ProvingKey` structs contain `h_query` (PoT).
/// Ensure the distribution channel strips this before the Decapper receives it,
/// or use a custom struct that enforces Leanness.
pub fn build_pvugc_vk_outer_from_pk_for<C: RecursionCycle>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
) -> PvugcVk<C::OuterE> {
    // Infer number of public inputs from VK
    // gamma_abc_g1 has length n_inputs + 1
    let n_inputs = pk_outer.vk.gamma_abc_g1.len() - 1;

    // Compute baked quotient points
    let q_points = compute_baked_points::<C>(pk_outer, vk_inner, n_inputs);

    PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        q_points,
    )
}

/// Default-cycle convenience wrapper around [`build_pvugc_vk_outer_from_pk_for`].
pub fn build_pvugc_vk_outer_from_pk(
    pk_outer: &Groth16PK<OuterE>,
    vk_inner: &InnerVk<DefaultCycle>,
) -> PvugcVk<OuterE> {
    build_pvugc_vk_outer_from_pk_for::<DefaultCycle>(pk_outer, vk_inner)
}

/// Compute the "Baked Quotient" points [Q_0, Q_1, ...] for the PVUGC target.
/// 
/// Q(x) = Q_0 + sum x_i Q_i = [H_const(x) * t(tau) / delta]_1
/// This allows the Decapper to subtract the constant quotient term from the target,
/// ensuring security against H-based attacks (as required by the Baked Quotient model).
fn compute_baked_points<C: RecursionCycle>(
    pk: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    n_inputs: usize,
) -> Vec<<C::OuterE as Pairing>::G1Affine> {
    // 1. Synthesize circuit to get matrices
    // We use dummy inputs because the circuit structure (QAP) is input-independent.
    let dummy_x = vec![InnerScalar::<C>::from(0u64); n_inputs];
    let dummy_proof = crate::outer_compressed::InnerProof::<C> {
        a: Default::default(),
        b: Default::default(),
        c: Default::default(),
    };
    let circuit = OuterCircuit::<C>::new(vk_inner.clone(), dummy_x, dummy_proof);
    
    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesis failed");
    let matrices = cs.to_matrices().expect("matrix extraction failed");
    
    let domain_size = cs.num_constraints().next_power_of_two();
    let domain = GeneralEvaluationDomain::<OuterScalar<C>>::new(domain_size)
        .expect("domain creation failed");
    
    // 2. Extract Public Columns (0..n_inputs)
    // Matrix format: Vec<Vec<(usize, Fr)>> where outer vec is by column (var index)
    // Column 0 is ONE constant.
    // Column 1..n_inputs are public inputs.
    let num_pub = n_inputs + 1;
    
    // Helper to convert column to polynomial in evaluation form (Lagrange basis)
    // Actually, ark-poly works with coefficients. We need to IFFT.
    // Fix type mismatch: The closure args need proper typing for r1cs::to_matrices output.
    let get_col_poly = |col_idx: usize, matrix: &[Vec<(OuterScalar<C>, usize)>]| -> DensePolynomial<OuterScalar<C>> {
        let mut evals = vec![OuterScalar::<C>::zero(); domain_size];
        
        for (row, terms) in matrix.iter().enumerate() {
            if row < domain_size {
                for &(val, var_idx) in terms {
                    if var_idx == col_idx {
                        evals[row] = val;
                    }
                }
            }
        }
        DensePolynomial::from_coefficients_slice(&domain.ifft(&evals))
    };

    // 3. Compute H_i polynomials
    // H(x) = (A(x)B(x) - C(x)) / Z(x)
    // For linear inputs: H(x) = H_0 + sum x_i H_i
    // H_0 comes from A_0 * B_0 - C_0
    // H_i comes from A_0 * B_i + A_i * B_0 - C_i (since A_i * B_j = 0 for pub-pub)
    
    let mut q_points = Vec::with_capacity(num_pub);
    
    // Pre-fetch column 0 polys
    let a0 = get_col_poly(0, &matrices.a);
    let b0 = get_col_poly(0, &matrices.b);
    let c0 = get_col_poly(0, &matrices.c);
    
    for i in 0..num_pub {
        let numerator = if i == 0 {
            // Constant term: A0 * B0 - C0
            &(&a0 * &b0) - &c0
        } else {
            // Linear term i: A0 * Bi + Ai * B0 - Ci
            let ai = get_col_poly(i, &matrices.a);
            let bi = get_col_poly(i, &matrices.b);
            let ci = get_col_poly(i, &matrices.c);
            &(&(&a0 * &bi) + &(&ai * &b0)) - &ci
        };
        
        let (h_poly, remainder) = numerator.divide_by_vanishing_poly(domain);
        assert!(remainder.is_zero(), "QAP division failed for baked quotient");
        
        // 4. Compute Q_i = [H_i(tau) * t(tau) / delta]_1
        // This is exactly an MSM of h_poly coefficients against pk.h_query
        // h_query corresponds to [tau^i * t(tau) / delta]_1
        
        // Pad coefficients to match h_query length if needed (h_poly degree is domain_size - 2)
        // pk.h_query length is usually domain_size - 1
        let coeffs = h_poly.coeffs;
        if coeffs.len() > pk.h_query.len() {
            panic!("H poly degree too high for PK parameters");
        }
        
        // Perform MSM
        // VariableBaseMSM::msm_bigint takes bits, let's use plain msm which takes scalars (converted to BigInt internally usually)
        let coeffs_bigint: Vec<_> = coeffs.iter().map(|c| c.into_bigint()).collect();
        let point: <C::OuterE as Pairing>::G1 = <C::OuterE as Pairing>::G1::msm_bigint(
            &pk.h_query[..coeffs.len()],
            &coeffs_bigint,
        );
        
        q_points.push(point.into_affine());
    }
    
    q_points
}

/// Build column bases from outer PVUGC VK for the specific statement
///
/// Column 0 aggregates the public Groth16 inputs; remaining columns correspond
/// to witness-only rows.
pub fn build_column_bases_outer_for<C: RecursionCycle>(
    pvugc_vk: &PvugcVk<C::OuterE>,
    vk_outer: &Groth16VK<C::OuterE>,
    public_inputs_outer: &[OuterScalar<C>],
) -> ColumnBases<C::OuterE> {
    use ark_ec::CurveGroup;

    let total_instance = vk_outer.gamma_abc_g1.len();
    assert!(total_instance > 0, "Groth16 VK must expose inputs");
    let expected_inputs = total_instance - 1;
    assert!(
        public_inputs_outer.len() == expected_inputs,
        "public input length mismatch"
    );

    let mut aggregate = pvugc_vk.beta_g2.into_group();
    aggregate += pvugc_vk.b_g2_query[0].into_group();

    for (idx, coeff) in public_inputs_outer.iter().enumerate() {
        let base = pvugc_vk
            .b_g2_query
            .get(1 + idx)
            .expect("pvugc_vk missing public columns");
        aggregate += base.into_group() * coeff;
    }

    pvugc_vk
        .enforce_isolated_witness_block(total_instance)
        .expect("outer PVUGC VK must guarantee witness isolation");
    pvugc_vk
        .enforce_public_residual_safe(public_inputs_outer)
        .expect("outer PVUGC VK must enforce public residual audit");

    let witness_cols: Vec<_> = pvugc_vk
        .b_g2_query
        .iter()
        .skip(total_instance)
        .cloned()
        .collect();

    let mut y_cols = Vec::with_capacity(1 + witness_cols.len());
    y_cols.push(aggregate.into_affine());
    y_cols.extend(witness_cols);

    ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    }
}

/// Default-cycle convenience wrapper around [`build_column_bases_outer_for`].
pub fn build_column_bases_outer(
    pvugc_vk: &PvugcVk<OuterE>,
    vk_outer: &Groth16VK<OuterE>,
    public_inputs_outer: &[OuterFr],
) -> ColumnBases<OuterE> {
    build_column_bases_outer_for::<DefaultCycle>(pvugc_vk, vk_outer, public_inputs_outer)
}

/// Arm column bases with ρ (outer curve)
///
/// This is identical to the inner arming logic, just on OuterE.
pub fn arm_columns_outer_for<C: RecursionCycle>(
    bases: &ColumnBases<C::OuterE>,
    rho: &OuterScalar<C>,
) -> ColumnArms<C::OuterE> {
    crate::arming::arm_columns(bases, rho).expect("arm_columns failed")
}

/// Default-cycle convenience wrapper around [`arm_columns_outer_for`].
pub fn arm_columns_outer(bases: &ColumnBases<OuterE>, rho: &OuterFr) -> ColumnArms<OuterE> {
    arm_columns_outer_for::<DefaultCycle>(bases, rho)
}

/// Compute Groth16 target R(vk_outer, x_outer) with Baked Quotient Subtraction
///
/// This is the PPE target on the OUTER verifier.
/// Converts inner public inputs to outer field before computing.
///
/// **BAKED QUOTIENT SECURITY:**
/// This function computes R_baked = R_raw * T_const^-1
/// Where T_const = e(Q(x), delta) is the constant quotient term.
/// This ensures the "Honest Decapper" can effectively subtract the quotient H(x)
/// without needing access to H-bases, while the adversary is prevented from forging it.
pub fn compute_target_outer_for<C: RecursionCycle>(
    vk_outer: &Groth16VK<C::OuterE>,
    pvugc_vk: &PvugcVk<C::OuterE>,
    public_inputs_inner: &[InnerScalar<C>],
) -> PairingOutput<C::OuterE> {
    // Convert inner Fr to outer Fr via bytes
    let x_outer: Vec<OuterScalar<C>> = public_inputs_inner
        .iter()
        .map(fr_inner_to_outer_for::<C>)
        .collect();

    // Compute L_raw(x) = γ_abc_g1_raw[0] + Σ x_i * γ_abc_g1_raw[i+1]
    let mut l = vk_outer.gamma_abc_g1_raw[0].into_group();
    for (i, xi) in x_outer.iter().enumerate() {
        l += vk_outer.gamma_abc_g1_raw[i + 1] * xi;
    }

    // Compute Q(x) = Q_0 + Σ x_i * Q_{i+1} (Baked Quotient Point)
    // q_const_points[0] is the constant term
    // q_const_points[1..] align with x_outer
    assert!(
        pvugc_vk.q_const_points.len() == x_outer.len() + 1,
        "PvugcVk baked points mismatch public inputs"
    );
    
    let mut q_sum = pvugc_vk.q_const_points[0].into_group();
    for (i, xi) in x_outer.iter().enumerate() {
        q_sum += pvugc_vk.q_const_points[i + 1] * xi;
    }
    
    // T_const = e(Q(x), delta)
    let t_const = C::OuterE::pairing(q_sum.into_affine(), vk_outer.delta_g2);

    // R = e(alpha,beta) * e(L_raw, gamma) - T_const
    // Note: Subtraction in GT corresponds to division in multiplicative group, 
    // or subtraction in additive representation of TargetField. 
    // Arkworks PairingOutput wraps TargetField which is usually Fp12.
    // Ops on PairingOutput (+, -) are additive in the extension field.
    // WAIT. Groth16 check is Product(Pairings) = 1.
    // Arkworks implementation often uses additive notation for pairings if the library does so?
    // ark_ec::pairing::PairingOutput implements Add, Sub.
    // Let's check what pairing returns.
    // Usually e(A,B) returns Fqk. The group is multiplicative.
    // But Arkworks might implement Add for PairingOutput as *multiplication* in the field?
    // Let's check documentation or assumption.
    // In `compute_target_outer_for` previously: `pairing(...) + pairing(...)`.
    // This implies additive notation (exponentiation in group).
    // So `pairing(A,B) - pairing(C,D)` effectively means `e(A,B) * e(C,D)^-1`.
    // Correct.
    
    C::OuterE::pairing(vk_outer.alpha_g1, vk_outer.beta_g2)
        + C::OuterE::pairing(l, vk_outer.gamma_g2)
        - t_const
}

/// Default-cycle convenience wrapper around [`compute_target_outer_for`].
pub fn compute_target_outer(
    vk_outer: &Groth16VK<OuterE>,
    pvugc_vk: &PvugcVk<OuterE>,
    public_inputs_inner: &[InnerFr],
) -> PairingOutput<OuterE> {
    compute_target_outer_for::<DefaultCycle>(vk_outer, pvugc_vk, public_inputs_inner)
}

/// Compute R^ρ for the outer target
pub fn compute_r_to_rho_outer_for<C: RecursionCycle>(
    r: &PairingOutput<C::OuterE>,
    rho: &OuterScalar<C>,
) -> PairingOutput<C::OuterE> {
    let r_to_rho = r.0.pow(&rho.into_bigint());
    PairingOutput(r_to_rho)
}

/// Default-cycle convenience wrapper around [`compute_r_to_rho_outer_for`].
pub fn compute_r_to_rho_outer(r: &PairingOutput<OuterE>, rho: &OuterFr) -> PairingOutput<OuterE> {
    compute_r_to_rho_outer_for::<DefaultCycle>(r, rho)
}
