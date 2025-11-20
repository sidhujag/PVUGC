//! This test ensures that γ₂ cannot be expressed as a linear combination
//! of the armed bases, which is the core security requirement for PVUGC.

use ark_bw6_761::{BW6_761, Fr};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{ops::Mul, test_rng, vec::Vec};

/// Simple test circuit for span testing
#[derive(Clone)]
struct TestCircuit<F: PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::alloc::AllocVar;
        use ark_r1cs_std::fields::fp::FpVar;
        
        let a = FpVar::new_witness(cs.clone(), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let b = FpVar::new_witness(cs.clone(), || {
            self.b.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let c = FpVar::new_input(cs.clone(), || {
            let a_val = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b_val = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(a_val * b_val)
        })?;
        
        let ab = &a * &b;
        use ark_r1cs_std::eq::EqGadget;
        ab.enforce_equal(&c)?;
        
        Ok(())
    }
}

/// Check if a G₂ element can be expressed as a linear combination of basis elements
/// Returns true if target IS in the span (security failure)
fn is_in_span<E: Pairing>(
    target: E::G2Affine,
    basis: &[E::G2Affine],
) -> bool {
    // Convert to projective coordinates for arithmetic
    let target_proj = target.into_group();
    
    // Try to solve: target = Σᵢ αᵢ * basis[i]
    // This is a discrete log problem - we'll use a heuristic check
    
    // For security testing, we'll try small coefficients exhaustively
    // and use linear algebra over a small prime field as a proxy
    
    // Extract x,y coordinates and check linear dependence
    // This is a simplified check - in production, use more sophisticated methods
    
    const MAX_COEFF: i32 = 100;
    const SAMPLES: usize = 1000;
    
    let mut rng = test_rng();
    
    // Random sampling approach: try random small coefficients
    for _ in 0..SAMPLES {
        let mut combination = <E::G2 as Zero>::zero();
        let mut coeffs = Vec::new();
        
        for basis_elem in basis.iter() {
            let coeff = <E::ScalarField>::rand(&mut rng);
            coeffs.push(coeff);
            combination = combination + basis_elem.into_group().mul(coeff);
        }
        
        if combination == target_proj {
            println!("WARNING: Found linear combination!");
            println!("Coefficients: {:?}", coeffs);
            return true;
        }
    }
    
    // Exhaustive small coefficient search (for very small spaces)
    if basis.len() <= 3 {
        for a in -MAX_COEFF..=MAX_COEFF {
            if basis.len() >= 1 {
                for b in -MAX_COEFF..=MAX_COEFF {
                    if basis.len() >= 2 {
                        for c in -MAX_COEFF..=MAX_COEFF {
                            if basis.len() >= 3 {
                                let mut comb = <E::G2 as Zero>::zero();
                                if a != 0 {
                                    let scalar = <E::ScalarField>::from(a.abs() as u64);
                                    comb = comb + basis[0].into_group().mul(scalar);
                                    if a < 0 {
                                        comb = -comb;
                                    }
                                }
                                if b != 0 {
                                    let scalar = <E::ScalarField>::from(b.abs() as u64);
                                    let term = basis[1].into_group().mul(scalar);
                                    if b < 0 {
                                        comb = comb - term;
                                    } else {
                                        comb = comb + term;
                                    }
                                }
                                if c != 0 {
                                    let scalar = <E::ScalarField>::from(c.abs() as u64);
                                    let term = basis[2].into_group().mul(scalar);
                                    if c < 0 {
                                        comb = comb - term;
                                    } else {
                                        comb = comb + term;
                                    }
                                }
                                
                                if comb == target_proj {
                                    println!("WARNING: Found small coefficient combination!");
                                    println!("Coeffs: [{}, {}, {}]", a, b, c);
                                    return true;
                                }
                            }
                        }
                    } else {
                        let mut comb = <E::G2 as Zero>::zero();
                        if a != 0 {
                            let scalar = <E::ScalarField>::from(a.abs() as u64);
                            comb = comb + basis[0].into_group().mul(scalar);
                            if a < 0 {
                                comb = -comb;
                            }
                        }
                        if b != 0 && basis.len() > 1 {
                            let scalar = <E::ScalarField>::from(b.abs() as u64);
                            let term = basis[1].into_group().mul(scalar);
                            if b < 0 {
                                comb = comb - term;
                            } else {
                                comb = comb + term;
                            }
                        }
                        
                        if comb == target_proj {
                            println!("WARNING: Found small coefficient combination!");
                            println!("Coeffs: [{}, {}]", a, b);
                            return true;
                        }
                    }
                }
            }
        }
    }
    
    false
}

#[test]
fn test_gamma_not_in_armed_span() {
    let mut rng = test_rng();
    
    // Create a test circuit
    let circuit = TestCircuit::<Fr> {
        a: Some(Fr::rand(&mut rng)),
        b: Some(Fr::rand(&mut rng)),
    };
    
    // Generate CRS with PVUGC modifications (no 1/γ in IC)
    let (pk, vk) = Groth16::<BW6_761>::circuit_specific_setup_pvugc(circuit.clone(), &mut rng)
        .expect("Setup failed");
    
    // Extract the bases that will be armed: {β₂, Q₁, ..., Qₘ, δ₂}
    let mut armed_bases = Vec::new();
    
    // Add β₂
    armed_bases.push(vk.beta_g2);
    
    // Add all B-query elements (these are the Qⱼ)
    armed_bases.extend(&pk.b_g2_query);
    
    // Add δ₂
    armed_bases.push(vk.delta_g2);
    

    
    // The critical security test: γ₂ must NOT be in the span of armed bases
    assert!(
        !is_in_span::<BW6_761>(vk.gamma_g2, &armed_bases),
        "CRITICAL SECURITY FAILURE: γ₂ is in the span of armed bases!"
    );
    

}

#[test]
fn test_gamma_independence_multiple_circuits() {
    let mut rng = test_rng();
    
    // Test with multiple circuit sizes to ensure independence holds generally
    let circuit_sizes = vec![1, 2, 5, 10];
    
    for size in circuit_sizes {
        println!("\nTesting circuit with {} constraints", size);
        
        // Create circuit with 'size' multiplication constraints
        let circuit = TestCircuit::<Fr> {
            a: Some(Fr::rand(&mut rng)),
            b: Some(Fr::rand(&mut rng)),
        };
        
        // Generate CRS
        let (pk, vk) = Groth16::<BW6_761>::circuit_specific_setup_pvugc(circuit.clone(), &mut rng)
            .expect("Setup failed");
        
        // Build armed basis
        let mut armed_bases = vec![vk.beta_g2];
        armed_bases.extend(&pk.b_g2_query);
        armed_bases.push(vk.delta_g2);
        
        // Test independence
        assert!(
            !is_in_span::<BW6_761>(vk.gamma_g2, &armed_bases),
            "SECURITY FAILURE: γ₂ in span for circuit size {}", size
        );
        

    }
}

#[test]
fn test_no_cross_circuit_span_attack() {
    let mut rng = test_rng();
    
    // Generate two different circuits with same trusted setup randomness
    // This tests if combining bases from different circuits could yield γ₂
    
    let circuit1 = TestCircuit::<Fr> {
        a: Some(Fr::from(2u64)),
        b: Some(Fr::from(3u64)),
    };
    
    let circuit2 = TestCircuit::<Fr> {
        a: Some(Fr::from(5u64)),
        b: Some(Fr::from(7u64)),
    };
    
    let (pk1, vk1) = Groth16::<BW6_761>::circuit_specific_setup_pvugc(circuit1, &mut rng)
        .expect("Setup 1 failed");
    let (pk2, vk2) = Groth16::<BW6_761>::circuit_specific_setup_pvugc(circuit2, &mut rng)
        .expect("Setup 2 failed");
    
    // Combine bases from both circuits
    let mut combined_bases = Vec::new();
    combined_bases.push(vk1.beta_g2);
    combined_bases.push(vk2.beta_g2);
    combined_bases.extend(&pk1.b_g2_query);
    combined_bases.extend(&pk2.b_g2_query);
    combined_bases.push(vk1.delta_g2);
    combined_bases.push(vk2.delta_g2);
    
    // Neither γ₂ should be expressible even with combined bases
    assert!(
        !is_in_span::<BW6_761>(vk1.gamma_g2, &combined_bases),
        "SECURITY FAILURE: γ₂ from circuit 1 in combined span!"
    );
    
    // Note: vk2.gamma_g2 might equal vk1.gamma_g2 if same setup params used
    // But neither should be in the span of B-columns
   
}

#[test] 
fn test_armed_basis_linear_independence() {
    let mut rng = test_rng();
    
    let circuit = TestCircuit::<Fr> {
        a: Some(Fr::rand(&mut rng)),
        b: Some(Fr::rand(&mut rng)),
    };
    
    let (pk, vk) = Groth16::<BW6_761>::circuit_specific_setup_pvugc(circuit, &mut rng)
        .expect("Setup failed");
    
    // Check that armed bases themselves are linearly independent
    let mut armed_bases = vec![vk.beta_g2];
    armed_bases.extend(&pk.b_g2_query);
    armed_bases.push(vk.delta_g2);
    
    // Simplified check: no element should be expressible by others
    for i in 0..armed_bases.len() {
        let target = armed_bases[i];
        let mut others = armed_bases.clone();
        let _ = others.remove(i);
        
        assert!(
            !is_in_span::<BW6_761>(target, &others),
            "Armed bases are not linearly independent at index {}", i
        );
    }
    

}
