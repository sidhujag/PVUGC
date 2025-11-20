#![no_main]

//! MSM Attack Fuzzer: Verify adversary cannot find coefficients to produce R^ρ with wrong witness
//! 
//! This fuzzer attempts to find Multi-Scalar Multiplication (MSM) coefficients that would
//! allow an adversary to compute the target R^ρ without knowing the correct witness.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_snark::SNARK;
use ark_std::{vec::Vec, rand::{SeedableRng, Rng}};

use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::ppe::{PvugcVk, build_one_sided_ppe, compute_groth16_target};

/// Test circuit: x (public) = y² (witness)
#[derive(Clone)]
struct SquareCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SquareCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let y_squared = &y * &y;
        x.enforce_equal(&y_squared)?;
        
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N {
        return None;
    }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    
    // Parse fuzzer input
    let x_bytes = if let Some(b) = take_bytes::<32>(&mut data) { b } else { return; };
    let seed_bytes = if let Some(b) = take_bytes::<8>(&mut data) { b } else { return; };
    let rho_bytes = if let Some(b) = take_bytes::<32>(&mut data) { b } else { return; };
    let search_iterations = if let Some([b]) = take_bytes::<1>(&mut data) { 
        (b as usize % 50) + 10 
    } else { 
        return; 
    };
    
    let x = Fr::from_le_bytes_mod_order(&x_bytes);
    let seed = u64::from_le_bytes(seed_bytes);
    let rho = Fr::from_le_bytes_mod_order(&rho_bytes);
    
    if rho.is_zero() {
        return;
    }
    
    // Setup deterministic circuit
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    
    // Create circuit with CORRECT witness
    let y_correct = x.sqrt().unwrap_or(Fr::zero());
    let correct_circuit = SquareCircuit {
        x: Some(x),
        y: Some(y_correct),
    };
    
    // Generate CRS
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(correct_circuit.clone(), &mut rng)
        .expect("Setup failed");
    
    // Build PVUGC structures
    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };
    
    // Get column bases
    let (y_bases, delta, _) = build_one_sided_ppe::<E>(&pvugc_vk, &vk, &[x])
        .expect("Failed to build PPE");
    
    // Arm the columns with ρ
    let y_cols_rho: Vec<G2Affine> = y_bases.iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();
    let delta_rho = (delta.into_group() * rho).into_affine();
    
    // Compute target R and R^ρ
    let _r = compute_groth16_target::<E>(&vk, &[x]).expect("Failed to compute R");
    let r_rho = <E as Pairing>::pairing(vk.alpha_g1, vk.beta_g2.into_group() * rho)
        + <E as Pairing>::pairing(vk.gamma_abc_g1[0], vk.gamma_g2.into_group() * rho);
    
    // Now try to find MSM coefficients with WRONG witness
    // Generate various wrong witnesses
    let wrong_witnesses = vec![
        Fr::zero(),
        Fr::one(),
        -y_correct,
        y_correct + Fr::one(),
        y_correct * Fr::from(2u64),
        Fr::rand(&mut rng),
    ];
    
    for wrong_y in wrong_witnesses {
        if wrong_y == y_correct {
            continue; // Skip the correct witness
        }
        
        // Try to create a "proof" with wrong witness
        let wrong_circuit = SquareCircuit {
            x: Some(x),
            y: Some(wrong_y),
        };
        
        // This should fail or produce invalid proof
        let proof_result = Groth16::<E>::prove(&pk, wrong_circuit, &mut rng);
        
        if let Ok(wrong_proof) = proof_result {
            // Even if we somehow got a proof with wrong witness,
            // it should NOT verify
            let verify_result = Groth16::<E>::verify(&vk, &[x], &wrong_proof);
            assert!(
                verify_result.is_err() || !verify_result.unwrap(),
                "Wrong witness produced valid proof!"
            );
        }
        
        // Now try MSM attack: find coefficients to directly construct R^ρ
        for _ in 0..search_iterations {
            // Sample random MSM coefficients
            let mut coeffs_g1 = Vec::new();
            let mut coeffs_g2 = Vec::new();
            
            // Random coefficients for G1 elements
            for _ in 0..vk.gamma_abc_g1.len() {
                let c = if let Some(b) = take_bytes::<32>(&mut data) {
                    Fr::from_le_bytes_mod_order(&b)
                } else {
                    Fr::rand(&mut rng)
                };
                coeffs_g1.push(c);
            }
            
            // Random coefficients for armed G2 elements
            for _ in 0..y_cols_rho.len() {
                let c = if let Some(b) = take_bytes::<32>(&mut data) {
                    Fr::from_le_bytes_mod_order(&b)
                } else {
                    Fr::rand(&mut rng)
                };
                coeffs_g2.push(c);
            }
            
            // Compute MSM combination in GT
            let mut msm_result = ark_ec::pairing::PairingOutput::<E>::zero();
            
            // Add contributions from G1 x G2^ρ pairings
            for (i, &c1) in coeffs_g1.iter().enumerate() {
                if i < vk.gamma_abc_g1.len() {
                    let g1_elem = vk.gamma_abc_g1[i].into_group() * c1;
                    
                    for (j, &_c2) in coeffs_g2.iter().enumerate() {
                        if j < y_cols_rho.len() {
                            msm_result += <E as Pairing>::pairing(
                                g1_elem,
                                y_cols_rho[j]
                            );
                        }
                    }
                    
                    // Also try pairing with δ^ρ
                    msm_result += <E as Pairing>::pairing(g1_elem, delta_rho);
                }
            }
            
            // Add α₁ x (armed bases) pairings
            for (j, &c2) in coeffs_g2.iter().enumerate() {
                if j < y_cols_rho.len() {
                    let g2_elem = y_cols_rho[j].into_group() * c2;
                    msm_result += <E as Pairing>::pairing(vk.alpha_g1, g2_elem);
                }
            }
            
            // Check if we accidentally found R^ρ (this should NEVER happen)
            if msm_result == r_rho {
                panic!(
                    "CRITICAL SECURITY FAILURE: Found MSM coefficients to compute R^ρ with wrong witness!\n\
                     Wrong y: {:?}, Correct y: {:?}\n\
                     G1 coeffs: {:?}\n\
                     G2 coeffs: {:?}",
                    wrong_y, y_correct, coeffs_g1, coeffs_g2
                );
            }
        }
    }
    
    // Also test with completely random MSM attempts (no witness at all)
    for _ in 0..search_iterations * 2 {
        // Pure random MSM in GT
        let num_g1 = (data.first().copied().unwrap_or(3) as usize % 5) + 1;
        let num_g2 = (data.get(1).copied().unwrap_or(3) as usize % 5) + 1;
        
        let mut msm_gt = ark_ec::pairing::PairingOutput::<E>::zero();
        
        for _ in 0..num_g1 {
            let g1_scalar = if let Some(b) = take_bytes::<32>(&mut data) {
                Fr::from_le_bytes_mod_order(&b)
            } else {
                Fr::rand(&mut rng)
            };
            
            let g1_point = if rng.gen_bool(0.5) {
                vk.alpha_g1.into_group() * g1_scalar
            } else if !vk.gamma_abc_g1.is_empty() {
                vk.gamma_abc_g1[0].into_group() * g1_scalar
            } else {
                <E as Pairing>::G1::generator() * g1_scalar
            };
            
            for _ in 0..num_g2 {
                let g2_scalar = if let Some(b) = take_bytes::<32>(&mut data) {
                    Fr::from_le_bytes_mod_order(&b)
                } else {
                    Fr::rand(&mut rng)
                };
                
                let g2_point = if !y_cols_rho.is_empty() && rng.gen_bool(0.7) {
                    y_cols_rho[rng.gen::<usize>() % y_cols_rho.len()].into_group() * g2_scalar
                } else {
                    delta_rho.into_group() * g2_scalar
                };
                
                msm_gt += <E as Pairing>::pairing(g1_point, g2_point);
            }
        }
        
        // This random MSM should never equal R^ρ
        assert_ne!(
            msm_gt, r_rho,
            "Random MSM accidentally produced R^ρ!"
        );
    }
});
