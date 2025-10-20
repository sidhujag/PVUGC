//! One-Sided PPE Construction for Groth16
//!
//! Builds PPE with target R(vk,x) = e(α,β) · e(L(x), γ)

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use ark_groth16::VerifyingKey as Groth16VK;
use ark_serialize::CanonicalSerialize;
use ark_std::Zero;
use sha2::{Digest, Sha256};

/// Compute the Groth16 verifier target R(vk, x)
///
/// R(vk,x) = e(α, β) · e(L(x), γ)
/// where L(x) = Σ x_i · [γ_i]₁
pub fn compute_groth16_target<E: Pairing>(
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> PairingOutput<E> {
    // Compute L(x) = vk.gamma_abc_g1[0] + Σ x_i · vk.gamma_abc_g1[i+1]
    let mut l = vk.gamma_abc_g1[0].into_group();

    for (i, x_i) in public_inputs.iter().enumerate() {
        l += vk.gamma_abc_g1[i + 1] * x_i;
    }

    // R = e(α, β) + e(L(x), γ)  (additive notation in arkworks)
    let r = E::pairing(vk.alpha_g1, vk.beta_g2) + E::pairing(l, vk.gamma_g2);

    r
}

/// Extract Y_j bases from Groth16 VK for B-side PPE
///
/// These are the statement-only G₂ bases that B is built from
/// PVUGC Verifying Key wrapper exposed at deposit time
#[derive(Clone, Debug)]
pub struct PvugcVk<E: Pairing> {
    pub beta_g2: E::G2Affine,
    pub delta_g2: E::G2Affine,
    pub b_g2_query: Vec<E::G2Affine>,
}

/// Extract Y_j bases from PVUGC-VK for B-side PPE
pub fn extract_y_bases<E: Pairing>(pvugc_vk: &PvugcVk<E>) -> Vec<E::G2Affine> {
    // Basis choice Y^{(B)} = {β₂} ∪ b_g2_query; δ₂ kept separate on C-side
    let mut y = Vec::with_capacity(1 + pvugc_vk.b_g2_query.len());
    y.push(pvugc_vk.beta_g2);
    y.extend_from_slice(&pvugc_vk.b_g2_query);
    y
}

/// Build one-sided PPE structure
///
/// IMPORTANT: Uses +δ (NOT -δ) to match Groth16 equation:
/// e(A,B) · e(C,δ) = e(α,β) · e(L(x),γ)
pub fn build_one_sided_ppe<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> (Vec<E::G2Affine>, E::G2Affine, PairingOutput<E>) {
    // Y_j bases for B-side from PVUGC-VK wrapper
    let y_bases = extract_y_bases(pvugc_vk);

    // +δ for C-side (CORRECT SIGN!)
    let delta = pvugc_vk.delta_g2;

    // Target R(vk, x)
    let target = compute_groth16_target(vk, public_inputs);

    (y_bases, delta, target)
}

/// Deterministically derive a thin Γ (|U| rows) from PVUGC-VK digests
pub fn derive_gamma_rademacher<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    num_rows: usize,
) -> Vec<Vec<E::ScalarField>> {
    // Seed = H("PVUGC/Γ" || vk_digest || beta || delta || hash(b_g2_query))
    let mut hasher = Sha256::new();
    hasher.update(b"PVUGC/GAMMA/v1");
    // vk digest (γ_abc_g1, α, β, γ, δ)
    let mut tmp = Vec::new();
    vk.alpha_g1.serialize_compressed(&mut tmp).unwrap();
    vk.beta_g2.serialize_compressed(&mut tmp).unwrap();
    vk.gamma_g2.serialize_compressed(&mut tmp).unwrap();
    vk.delta_g2.serialize_compressed(&mut tmp).unwrap();
    for g in &vk.gamma_abc_g1 {
        g.serialize_compressed(&mut tmp).unwrap();
    }
    hasher.update(&tmp);
    tmp.clear();
    pvugc_vk.beta_g2.serialize_compressed(&mut tmp).unwrap();
    pvugc_vk.delta_g2.serialize_compressed(&mut tmp).unwrap();
    hasher.update(&tmp);
    tmp.clear();
    for y in &pvugc_vk.b_g2_query {
        y.serialize_compressed(&mut tmp).unwrap();
    }
    let b_query_digest = Sha256::digest(&tmp);
    hasher.update(&b_query_digest);
    let seed = hasher.finalize();

    // Expand to Rademacher entries in {-1,0,+1}; bias sparse 0s lightly
    let cols = 1 + pvugc_vk.b_g2_query.len(); // {β} ∪ b_g2_query
    let mut gamma: Vec<Vec<E::ScalarField>> = Vec::with_capacity(num_rows);
    let mut ctr: u64 = 0;
    while gamma.len() < num_rows {
        let mut row = Vec::with_capacity(cols);
        for j in 0..cols {
            let mut h = Sha256::new();
            h.update(&seed);
            h.update(&ctr.to_le_bytes());
            h.update(&j.to_le_bytes());
            let out = h.finalize();
            let v = out[0] % 3; // 0,1,2
            let sf = match v {
                0 => E::ScalarField::from(-1i64),
                1 => E::ScalarField::from(0u64),
                _ => E::ScalarField::from(1u64),
            };
            row.push(sf);
        }
        // Avoid all-zero rows
        let mut nonzero = false;
        for c in &row {
            if !c.is_zero() {
                nonzero = true;
                break;
            }
        }
        if nonzero {
            gamma.push(row);
        }
        ctr += 1;
    }
    gamma
}

/// Validate subgroup membership for PVUGC-VK G₂ elements
pub fn validate_pvugc_vk_subgroups<E: Pairing>(pvugc_vk: &PvugcVk<E>) -> bool {
    // All G₂ elements must lie in the prime-order subgroup
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let is_good = |g: &E::G2Affine| {
        if g.is_zero() {
            return true;
        }

        g.mul_bigint(order).is_zero()
    };

    if pvugc_vk.beta_g2.is_zero() || !is_good(&pvugc_vk.beta_g2) {
        return false;
    }

    if pvugc_vk.delta_g2.is_zero() || !is_good(&pvugc_vk.delta_g2) {
        return false;
    }

    if pvugc_vk.b_g2_query.iter().any(|g| !is_good(g)) {
        return false;
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_groth16::Groth16;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_snark::SNARK;

    type E = Bls12_381;

    // Simple test circuit
    #[derive(Clone)]
    struct TestCircuit {
        pub x: Option<Fr>,
        pub y: Option<Fr>,
    }
    
    impl ConstraintSynthesizer<Fr> for TestCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            use ark_r1cs_std::eq::EqGadget;
            use ark_r1cs_std::fields::fp::FpVar;
            use ark_r1cs_std::prelude::*;

            let x_var = FpVar::new_input(cs.clone(), || {
                self.x.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let y_var = FpVar::new_witness(cs.clone(), || {
                self.y.ok_or(SynthesisError::AssignmentMissing)
            })?;

            let y_squared = &y_var * &y_var;
            x_var.enforce_equal(&y_squared)?;

            Ok(())
        }
    }
    
    #[test]
    fn test_compute_r_target() {
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(0);

        // Setup Groth16
        let circuit = TestCircuit {
            x: Some(Fr::from(25u64)),
            y: Some(Fr::from(5u64)),
        };
        let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();

        let public_inputs = vec![Fr::from(25u64)];

        // Compute R(vk, x)
        let r = compute_groth16_target(&vk, &public_inputs);

        // R should be non-trivial
        assert_ne!(r, PairingOutput::<E>::zero());

        // R should be deterministic
        let r2 = compute_groth16_target(&vk, &public_inputs);
        assert_eq!(r, r2);
    }
    
    #[test]
    fn test_different_statements_different_r() {
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(1);

        let circuit = TestCircuit {
            x: Some(Fr::from(25u64)),
            y: Some(Fr::from(5u64)),
        };
        let (_, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();

        // Two different statements (different public inputs)
        let inputs1 = vec![Fr::from(25u64)];
        let inputs2 = vec![Fr::from(49u64)];

        let r1 = compute_groth16_target(&vk, &inputs1);
        let r2 = compute_groth16_target(&vk, &inputs2);

        // Different statements → different R
        assert_ne!(r1, r2);
    }

    #[test]
    fn test_validate_pvugc_vk_subgroups_rejects_bad_points() {
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(42);

        let circuit = TestCircuit {
            x: Some(Fr::from(25u64)),
            y: Some(Fr::from(5u64)),
        };
        let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();

        let pvugc_vk: PvugcVk<E> = PvugcVk {
            beta_g2: vk.beta_g2,
            delta_g2: vk.delta_g2,
            b_g2_query: pk.b_g2_query.clone(),
        };

        assert!(validate_pvugc_vk_subgroups(&pvugc_vk));

        // Zero beta should be rejected
        let mut bad_beta = pvugc_vk.clone();
        bad_beta.beta_g2 = <E as Pairing>::G2Affine::identity();
        assert!(!validate_pvugc_vk_subgroups(&bad_beta));

        // Zero delta should be rejected
        let mut bad_delta = pvugc_vk.clone();
        bad_delta.delta_g2 = <E as Pairing>::G2Affine::identity();
        assert!(!validate_pvugc_vk_subgroups(&bad_delta));

        // Zero entries in the query vector are allowed
        let mut zero_query_vk = pvugc_vk.clone();
        if let Some(first) = zero_query_vk.b_g2_query.first_mut() {
            *first = <E as Pairing>::G2Affine::identity();
        }
        assert!(validate_pvugc_vk_subgroups(&zero_query_vk));
    }
}

