//! Global test fixtures with disk caching

use once_cell::sync::Lazy;
use std::sync::{Mutex, Arc};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use ark_snark::SNARK;
use ark_groth16::Groth16;

use crate::outer_compressed::{InnerE, OuterE, InnerFr, OuterFr};
use crate::test_circuits::AddCircuit;

/// Global fixture: Inner and Outer PK/VK
#[derive(Clone)]
pub struct GlobalFixture {
    pub pk_inner: Arc<ark_groth16::ProvingKey<InnerE>>,
    pub vk_inner: Arc<ark_groth16::VerifyingKey<InnerE>>,
    pub pk_outer: Arc<ark_groth16::ProvingKey<OuterE>>,
    pub vk_outer: Arc<ark_groth16::VerifyingKey<OuterE>>,
    pub pvugc_vk: crate::ppe::PvugcVk<OuterE>,
}

/// Global fixture: Generated once per process
pub static GLOBAL_FIXTURE: Lazy<Mutex<GlobalFixture>> = Lazy::new(|| {
    let mut rng = StdRng::seed_from_u64(999999);
    
    // Inner keys: AddCircuit on BLS12-377
    let circuit_inner = AddCircuit {
        x: Some(InnerFr::from(11u64)),
        y: Some(InnerFr::from(4u64)),
        z: Some(InnerFr::from(7u64)),
    };
    let (pk_inner, vk_inner) = Groth16::<InnerE>::circuit_specific_setup(circuit_inner, &mut rng).unwrap();
    
    // Outer keys: AddCircuit directly on BW6-761
    let circuit_outer = AddCircuit {
        x: Some(OuterFr::from(11u64)),
        y: Some(OuterFr::from(4u64)),
        z: Some(OuterFr::from(7u64)),
    };
    let (pk_outer, vk_outer) = Groth16::<OuterE>::circuit_specific_setup(circuit_outer, &mut rng).unwrap();
    
    // Build PvugcVk with Arc-wrapped b_g2_query
    let pvugc_vk = crate::ppe::PvugcVk {
        beta_g2: vk_outer.beta_g2,
        delta_g2: vk_outer.delta_g2,
        b_g2_query: std::sync::Arc::new(pk_outer.b_g2_query.clone()),
    };
    
    let fx = GlobalFixture { 
        pk_inner: Arc::new(pk_inner),
        vk_inner: Arc::new(vk_inner),
        pk_outer: Arc::new(pk_outer),
        vk_outer: Arc::new(vk_outer),
        pvugc_vk,
    };
    
    Mutex::new(fx)
});

/// Get the global fixture
pub fn get_fixture() -> GlobalFixture {
    let guard = GLOBAL_FIXTURE.lock().unwrap();
    guard.clone()
}

