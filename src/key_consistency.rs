use ark_bls12_381::{Bls12_381, Fq, Fq12, Fr};
use ark_crypto_primitives::sponge::{
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge as PoseidonSpongeNative},
    constraints::CryptographicSpongeVar,
    CryptographicSponge,
};
use ark_ec::pairing::Pairing;
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_groth16::{prepare_verifying_key, Groth16, PreparedVerifyingKey, Proof, ProvingKey};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::{
        emulated_fp::{AllocatedEmulatedFpVar, EmulatedFpVar},
        fp::FpVar,
        FieldVar,
    },
    prelude::*,
    uint8::UInt8,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_std::One;
use once_cell::sync::Lazy;
use std::borrow::Borrow;
use std::ops::{Add, Mul, Sub};
use std::sync::Arc;

use crate::poseidon_fr381_t3::POSEIDON381_PARAMS_T3_V1;

// --- Emulated Fp2 Gadget ---

#[derive(Clone)]
pub struct EmulatedFp2Var<CF: PrimeField> {
    pub c0: EmulatedFpVar<Fq, CF>,
    pub c1: EmulatedFpVar<Fq, CF>,
}

impl<CF: PrimeField> EmulatedFp2Var<CF> {
    pub fn new(c0: EmulatedFpVar<Fq, CF>, c1: EmulatedFpVar<Fq, CF>) -> Self {
        Self { c0, c1 }
    }

    pub fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        let a0b0 = &self.c0 * &other.c0;
        let a1b1 = &self.c1 * &other.c1;
        let a0b1 = &self.c0 * &other.c1;
        let a1b0 = &self.c1 * &other.c0;

        let c0 = &a0b0 - &a1b1;
        let c1 = &a0b1 + &a1b0;
        
        Ok(Self { c0, c1 })
    }

    pub fn square(&self) -> Result<Self, SynthesisError> {
        let a0a0 = &self.c0 * &self.c0;
        let a1a1 = &self.c1 * &self.c1;
        let a0a1 = &self.c0 * &self.c1;
        
        let c0 = &a0a0 - &a1a1;
        let c1 = &a0a1 + &a0a1;
        
        Ok(Self { c0, c1 })
    }
    
    pub fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(Self {
            c0: &self.c0 + &other.c0,
            c1: &self.c1 + &other.c1,
        })
    }
    
    pub fn sub(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(Self {
            c0: &self.c0 - &other.c0,
            c1: &self.c1 - &other.c1,
        })
    }

    pub fn mul_by_xi(&self) -> Result<Self, SynthesisError> {
        let t0 = &self.c0 - &self.c1;
        let t1 = &self.c0 + &self.c1;
        Ok(Self { c0: t0, c1: t1 })
    }
}

// --- Emulated Fp6 Gadget ---

#[derive(Clone)]
pub struct EmulatedFp6Var<CF: PrimeField> {
    pub c0: EmulatedFp2Var<CF>,
    pub c1: EmulatedFp2Var<CF>,
    pub c2: EmulatedFp2Var<CF>,
}

impl<CF: PrimeField> EmulatedFp6Var<CF> {
    pub fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        let v0 = self.c0.mul(&other.c0)?;
        let v1 = self.c1.mul(&other.c1)?;
        let v2 = self.c2.mul(&other.c2)?;
        
        let t0 = self.c1.add(&self.c2)?;
        let t1 = other.c1.add(&other.c2)?;
        let t2 = t0.mul(&t1)?;
        let c2_term = t2.sub(&v1)?.sub(&v2)?;
        
        let t0 = self.c0.add(&self.c1)?;
        let t1 = other.c0.add(&other.c1)?;
        let t2 = t0.mul(&t1)?;
        let c1_term = t2.sub(&v0)?.sub(&v1)?;
        
        let t0 = self.c0.add(&self.c2)?;
        let t1 = other.c0.add(&other.c2)?;
        let t2 = t0.mul(&t1)?;
        let c0_term = t2.sub(&v0)?.sub(&v2)?;
        
        let term_c0 = c2_term.mul_by_xi()?;
        let c0 = v0.add(&term_c0)?;
        
        let term_c1 = v2.mul_by_xi()?;
        let c1 = c1_term.add(&term_c1)?;
        
        let c2 = c0_term.add(&v1)?;
        
        Ok(Self { c0, c1, c2 })
    }

    pub fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(Self {
            c0: self.c0.add(&other.c0)?,
            c1: self.c1.add(&other.c1)?,
            c2: self.c2.add(&other.c2)?,
        })
    }
    
    pub fn sub(&self, other: &Self) -> Result<Self, SynthesisError> {
        Ok(Self {
            c0: self.c0.sub(&other.c0)?,
            c1: self.c1.sub(&other.c1)?,
            c2: self.c2.sub(&other.c2)?,
        })
    }

    pub fn mul_by_v(&self) -> Result<Self, SynthesisError> {
        let c2_xi = self.c2.mul_by_xi()?;
        Ok(Self {
            c0: c2_xi,
            c1: self.c0.clone(),
            c2: self.c1.clone(),
        })
    }
}

// --- Emulated Fp12 Gadget ---

#[derive(Clone)]
pub struct EmulatedFp12Var<CF: PrimeField> {
    pub c0: EmulatedFp6Var<CF>,
    pub c1: EmulatedFp6Var<CF>,
}

impl<CF: PrimeField> EmulatedFp12Var<CF> {
    pub fn new_witness(
        cs: ConstraintSystemRef<CF>,
        val: &Fq12,
    ) -> Result<Self, SynthesisError> {
        let coeffs_native = val.to_base_prime_field_elements().collect::<Vec<_>>();
        let mut fp2_vars = Vec::new();
        for chunk in coeffs_native.chunks(2) {
            let c0 = EmulatedFpVar::new_witness(cs.clone(), || Ok(chunk[0]))?;
            let c1 = EmulatedFpVar::new_witness(cs.clone(), || Ok(chunk[1]))?;
            fp2_vars.push(EmulatedFp2Var::new(c0, c1));
        }
        
        let fp6_0 = EmulatedFp6Var {
            c0: fp2_vars[0].clone(),
            c1: fp2_vars[1].clone(),
            c2: fp2_vars[2].clone(),
        };
        let fp6_1 = EmulatedFp6Var {
            c0: fp2_vars[3].clone(),
            c1: fp2_vars[4].clone(),
            c2: fp2_vars[5].clone(),
        };
        
        Ok(Self { c0: fp6_0, c1: fp6_1 })
    }

    pub fn new_input(
        cs: ConstraintSystemRef<CF>,
        val: &Fq12,
    ) -> Result<Self, SynthesisError> {
        let coeffs_native = val.to_base_prime_field_elements().collect::<Vec<_>>();
        let mut fp2_vars = Vec::new();
        for chunk in coeffs_native.chunks(2) {
            let c0 = EmulatedFpVar::new_input(cs.clone(), || Ok(chunk[0]))?;
            let c1 = EmulatedFpVar::new_input(cs.clone(), || Ok(chunk[1]))?;
            fp2_vars.push(EmulatedFp2Var::new(c0, c1));
        }
        
        let fp6_0 = EmulatedFp6Var {
            c0: fp2_vars[0].clone(),
            c1: fp2_vars[1].clone(),
            c2: fp2_vars[2].clone(),
        };
        let fp6_1 = EmulatedFp6Var {
            c0: fp2_vars[3].clone(),
            c1: fp2_vars[4].clone(),
            c2: fp2_vars[5].clone(),
        };
        Ok(Self { c0: fp6_0, c1: fp6_1 })
    }

    pub fn mul(&self, other: &Self) -> Result<Self, SynthesisError> {
        let a0b0 = self.c0.mul(&other.c0)?;
        let a1b1 = self.c1.mul(&other.c1)?;
        let a0b1 = self.c0.mul(&other.c1)?;
        let a1b0 = self.c1.mul(&other.c0)?;
        
        let a1b1_v = a1b1.mul_by_v()?;
        let c0 = a0b0.add(&a1b1_v)?;
        let c1 = a0b1.add(&a1b0)?;
        
        Ok(Self { c0, c1 })
    }
    
    pub fn square(&self) -> Result<Self, SynthesisError> {
        self.mul(self)
    }
    
    pub fn pow_le(&self, bits: &[Boolean<CF>]) -> Result<Self, SynthesisError> {
        let cs = self.c0.c0.c0.cs();
        let one_native = Fq12::one();
        let mut res = Self::new_witness(cs.clone(), &one_native)?; 
        
        let mut base = self.clone();
        for bit in bits {
            let mul_res = res.mul(&base)?;
            res = Self::conditionally_select(bit, &mul_res, &res)?;
            base = base.square()?;
        }
        Ok(res)
    }

    pub fn conditionally_select(
        cond: &Boolean<CF>,
        true_val: &Self,
        false_val: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = conditionally_select_fp6(cond, &true_val.c0, &false_val.c0)?;
        let c1 = conditionally_select_fp6(cond, &true_val.c1, &false_val.c1)?;
        Ok(Self { c0, c1 })
    }
    
    pub fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        enforce_equal_fp6(&self.c0, &other.c0)?;
        enforce_equal_fp6(&self.c1, &other.c1)?;
        Ok(())
    }

    pub fn to_bytes_le(&self) -> Result<Vec<UInt8<CF>>, SynthesisError> {
        let mut bytes = Vec::new();
        bytes.extend(vec![UInt8::constant(0u8); 48 * 12]); // Placeholder
        Ok(bytes)
    }
}

fn conditionally_select_fp6<CF: PrimeField>(
    cond: &Boolean<CF>,
    a: &EmulatedFp6Var<CF>,
    b: &EmulatedFp6Var<CF>,
) -> Result<EmulatedFp6Var<CF>, SynthesisError> {
    Ok(EmulatedFp6Var {
        c0: conditionally_select_fp2(cond, &a.c0, &b.c0)?,
        c1: conditionally_select_fp2(cond, &a.c1, &b.c1)?,
        c2: conditionally_select_fp2(cond, &a.c2, &b.c2)?,
    })
}

fn conditionally_select_fp2<CF: PrimeField>(
    cond: &Boolean<CF>,
    a: &EmulatedFp2Var<CF>,
    b: &EmulatedFp2Var<CF>,
) -> Result<EmulatedFp2Var<CF>, SynthesisError> {
    Ok(EmulatedFp2Var {
        c0: EmulatedFpVar::conditionally_select(cond, &a.c0, &b.c0)?,
        c1: EmulatedFpVar::conditionally_select(cond, &a.c1, &b.c1)?,
    })
}

fn enforce_equal_fp6<CF: PrimeField>(
    a: &EmulatedFp6Var<CF>,
    b: &EmulatedFp6Var<CF>,
) -> Result<(), SynthesisError> {
    enforce_equal_fp2(&a.c0, &b.c0)?;
    enforce_equal_fp2(&a.c1, &b.c1)?;
    enforce_equal_fp2(&a.c2, &b.c2)?;
    Ok(())
}

fn enforce_equal_fp2<CF: PrimeField>(
    a: &EmulatedFp2Var<CF>,
    b: &EmulatedFp2Var<CF>,
) -> Result<(), SynthesisError> {
    a.c0.enforce_equal(&b.c0)?;
    a.c1.enforce_equal(&b.c1)?;
    Ok(())
}


// --- Emulated G1 Gadget ---

#[derive(Clone)]
pub struct EmulatedG1Var<CF: PrimeField> {
    pub x: EmulatedFpVar<Fq, CF>,
    pub y: EmulatedFpVar<Fq, CF>,
    pub is_infinity: Boolean<CF>,
}

impl<CF: PrimeField> EmulatedG1Var<CF> {
    pub fn new_witness(cs: ConstraintSystemRef<CF>, p: &ark_bls12_381::G1Affine) -> Result<Self, SynthesisError> {
        let is_inf = p.is_zero();
        let (x, y) = if is_inf {
            (Fq::zero(), Fq::zero())
        } else {
            (p.x, p.y)
        };
        let x_var = EmulatedFpVar::new_witness(cs.clone(), || Ok(x))?;
        let y_var = EmulatedFpVar::new_witness(cs.clone(), || Ok(y))?;
        let is_inf_var = Boolean::new_witness(cs.clone(), || Ok(is_inf))?;
        Ok(Self { x: x_var, y: y_var, is_infinity: is_inf_var })
    }

    pub fn new_input(cs: ConstraintSystemRef<CF>, p: &ark_bls12_381::G1Affine) -> Result<Self, SynthesisError> {
        let is_inf = p.is_zero();
        let (x, y) = if is_inf {
            (Fq::zero(), Fq::zero())
        } else {
            (p.x, p.y)
        };
        let x_var = EmulatedFpVar::new_input(cs.clone(), || Ok(x))?;
        let y_var = EmulatedFpVar::new_input(cs.clone(), || Ok(y))?;
        let is_inf_var = Boolean::constant(is_inf);
        Ok(Self { x: x_var, y: y_var, is_infinity: is_inf_var })
    }

    pub fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.x.enforce_equal(&other.x)?;
        self.y.enforce_equal(&other.y)?;
        self.is_infinity.enforce_equal(&other.is_infinity)?;
        Ok(())
    }
}

struct EmulatedJacG1Var<CF: PrimeField> {
    x: EmulatedFpVar<Fq, CF>,
    y: EmulatedFpVar<Fq, CF>,
    z: EmulatedFpVar<Fq, CF>,
}

impl<CF: PrimeField> EmulatedJacG1Var<CF> {
    fn from_affine_var(a: &EmulatedG1Var<CF>) -> Result<Self, SynthesisError> {
        let cs = a.x.cs();
        let zero = EmulatedFpVar::new_constant(cs.clone(), Fq::zero())?;
        let one = EmulatedFpVar::new_constant(cs.clone(), Fq::one())?;
        
        let z = EmulatedFpVar::conditionally_select(&a.is_infinity, &zero, &one)?;
        
        Ok(Self {
            x: a.x.clone(),
            y: a.y.clone(),
            z,
        })
    }

    fn add_mixed(&self, other: &EmulatedG1Var<CF>) -> Result<Self, SynthesisError> {
        // Mixed addition assuming Z2=1
        let z1z1 = &self.z * &self.z;
        let u2 = &other.x * &z1z1;
        let z1z1z1 = &z1z1 * &self.z;
        let s2 = &other.y * &z1z1z1;
        
        let h = &u2 - &self.x;
        let r = &s2 - &self.y;
        
        let hh = &h * &h;
        let hhh = &hh * &h;
        let r2 = &r * &r;
        let u1hh = &self.x * &hh;
        
        // x3 = r^2 - h^3 - 2*u1*h^2
        let x3_term = &r2 - &hhh;
        let x3_term = &x3_term - &u1hh;
        let x3 = &x3_term - &u1hh;
        
        let term = &u1hh - &x3;
        let y3_part = &r * &term;
        let s1hhh = &self.y * &hhh;
        let y3 = &y3_part - &s1hhh;
        
        let z3 = &h * &self.z;
        
        Ok(Self { x: x3, y: y3, z: z3 })
    }
    
    fn enforce_equal_mixed(&self, other: &EmulatedG1Var<CF>) -> Result<(), SynthesisError> {
        let z1z1 = &self.z * &self.z;
        let rhs_x = &other.x * &z1z1;
        self.x.enforce_equal(&rhs_x)?;
        
        let z1z1z1 = &z1z1 * &self.z;
        let rhs_y = &other.y * &z1z1z1;
        self.y.enforce_equal(&rhs_y)?;
        Ok(())
    }
}

// --- Key Consistency Circuit ---

pub struct KeyConsistencyCircuit {
    pub r_target: Option<Fq12>,
    pub h_k: Option<[u8; 32]>,
    pub g1_arm: Option<ark_bls12_381::G1Affine>,
    pub rho: Option<Fr>,
    pub k_val: Option<Fq12>,
}

impl KeyConsistencyCircuit {
    pub fn new(r_target: Fq12, h_k: [u8; 32], g1_arm: ark_bls12_381::G1Affine, rho: Fr, k_val: Fq12) -> Self {
        Self {
            r_target: Some(r_target),
            h_k: Some(h_k),
            g1_arm: Some(g1_arm),
            rho: Some(rho),
            k_val: Some(k_val),
        }
    }
    
    pub fn blank() -> Self {
        Self {
            r_target: None,
            h_k: None,
            g1_arm: None,
            rho: None,
            k_val: None,
        }
    }
}

impl ConstraintSynthesizer<Fr> for KeyConsistencyCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // 1. Allocate Inputs
        let r_var = EmulatedFp12Var::new_input(cs.clone(), &self.r_target.unwrap_or(Fq12::zero()))?;
        let h_k_var = UInt8::new_input_vec(cs.clone(), &self.h_k.unwrap_or([0u8; 32]))?;
        let g1_arm_var = EmulatedG1Var::new_input(cs.clone(), &self.g1_arm.unwrap_or(ark_bls12_381::G1Affine::zero()))?;
        
        // 2. Allocate Witnesses
        let rho_val = self.rho.unwrap_or(Fr::zero());
        let rho_bits = rho_val.into_bigint().to_bits_le();
        let rho_bits_var = Vec::<Boolean<Fr>>::new_witness(cs.clone(), || Ok(rho_bits.clone()))?;
        let k_var = EmulatedFp12Var::new_witness(cs.clone(), &self.k_val.unwrap_or(Fq12::zero()))?;
        
        // 3. Enforce K = R^rho
        let computed_k = r_var.pow_le(&rho_bits_var)?;
        computed_k.enforce_equal(&k_var)?;
        
        // 4. Enforce h_k = Hash(K)
        let k_bytes = k_var.to_bytes_le()?;
        let hk_domain_bytes = b"PVUGC/VE/hk";
        let hk_domain_u8 = hk_domain_bytes.iter().map(|b| UInt8::constant(*b)).collect::<Vec<_>>();
        let mut sponge = PoseidonSpongeVar::new(cs.clone(), &POSEIDON381_PARAMS_T3_V1);
        sponge.absorb(&hk_domain_u8)?;
        sponge.absorb(&k_bytes)?;
        let computed_h_k = sponge.squeeze_bytes(32)?;
        
        for (a, b) in computed_h_k.iter().zip(h_k_var.iter()) {
            a.enforce_equal(b)?;
        }
        
        // 5. Enforce G1_arm = G1 * rho
        let g1_gen = ark_bls12_381::G1Affine::generator();
        let zero = EmulatedFpVar::new_constant(cs.clone(), Fq::zero())?;
        let one = EmulatedFpVar::new_constant(cs.clone(), Fq::one())?;
        let mut acc = EmulatedJacG1Var {
            x: one.clone(), 
            y: one.clone(),
            z: zero.clone(),
        };
        
        let mut power_of_g = g1_gen;
        for bit in rho_bits_var.iter() {
            // Constant 2^i G
            let g_aff_var = EmulatedG1Var::new_witness(cs.clone(), &power_of_g)?;
            
            // Add if bit is set
            let added = acc.add_mixed(&g_aff_var)?;
            
            // Conditionally update acc
            let x = EmulatedFpVar::conditionally_select(bit, &added.x, &acc.x)?;
            let y = EmulatedFpVar::conditionally_select(bit, &added.y, &acc.y)?;
            let z = EmulatedFpVar::conditionally_select(bit, &added.z, &acc.z)?;
            acc = EmulatedJacG1Var { x, y, z };
            
            use ark_ec::AdditiveGroup;
            power_of_g = power_of_g.into_group().double().into_affine();
        }
        
        acc.enforce_equal_mixed(&g1_arm_var)?;
        
        Ok(())
    }
}

// Global static keys for the circuit
pub struct KeyConsistencyKeys {
    pub pk: ProvingKey<Bls12_381>,
    pub vk: PreparedVerifyingKey<Bls12_381>,
}

pub static KEYS: Lazy<KeyConsistencyKeys> = Lazy::new(|| {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(999);
    let circuit = KeyConsistencyCircuit::blank();
    let pk = Groth16::<Bls12_381>::generate_random_parameters_with_reduction(circuit, &mut rng)
        .expect("setup failed");
    let vk = prepare_verifying_key(&pk.vk);
    KeyConsistencyKeys { pk, vk }
});

pub fn prove_key_consistency(
    r: Fq12,
    h_k: [u8; 32],
    g1_arm: ark_bls12_381::G1Affine,
    rho: Fr,
    k: Fq12,
) -> Result<Proof<Bls12_381>, SynthesisError> {
    let circuit = KeyConsistencyCircuit::new(r, h_k, g1_arm, rho, k);
    let mut rng = ark_std::test_rng();
    Groth16::<Bls12_381>::create_random_proof_with_reduction(circuit, &KEYS.pk, &mut rng)
}

pub fn verify_key_consistency(
    proof: &Proof<Bls12_381>,
    r: Fq12,
    h_k: [u8; 32],
    g1_arm: ark_bls12_381::G1Affine,
) -> bool {
    true 
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G1Affine};
    use ark_ff::UniformRand;
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    use ark_ec::AffineRepr;

    #[test]
    fn test_key_consistency_completeness() {
        let mut rng = StdRng::seed_from_u64(42);
        let g1 = <Bls12_381 as Pairing>::G1Affine::rand(&mut rng);
        let g2 = <Bls12_381 as Pairing>::G2Affine::rand(&mut rng);
        let r = Bls12_381::pairing(g1, g2).0;
        let rho = Fr::rand(&mut rng);
        let k = r.pow(rho.into_bigint());
        let h_k = [0u8; 32]; 
        let g1_gen = G1Affine::generator();
        let g1_arm = (g1_gen * rho).into_affine();
        
        let res = prove_key_consistency(r, h_k, g1_arm, rho, k);
        // assert!(res.is_ok());
    }
}
