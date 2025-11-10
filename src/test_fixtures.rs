//! Global test fixtures with disk caching

use once_cell::sync::Lazy;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

use crate::outer_compressed::{
    self, cycles::Mnt4Mnt6Cycle, DefaultCycle, InnerScalar, OuterScalar, RecursionCycle,
};
use crate::test_circuits::AddCircuit;

/// Generic global fixture: Inner and Outer PK/VK for a recursion cycle
#[derive(Clone)]
pub struct GlobalFixture<C: RecursionCycle> {
    pub pk_inner: Arc<ark_groth16::ProvingKey<C::InnerE>>,
    pub vk_inner: Arc<ark_groth16::VerifyingKey<C::InnerE>>,
    pub pk_outer: Arc<ark_groth16::ProvingKey<C::OuterE>>,
    pub vk_outer: Arc<ark_groth16::VerifyingKey<C::OuterE>>,
    pub pvugc_vk: crate::ppe::PvugcVk<C::OuterE>,
    pub pk_outer_recursive: Arc<ark_groth16::ProvingKey<C::OuterE>>,
    pub vk_outer_recursive: Arc<ark_groth16::VerifyingKey<C::OuterE>>,
    pub pvugc_vk_outer_recursive: crate::ppe::PvugcVk<C::OuterE>,
    pub outer_setup_time: std::time::Duration,
}

impl<C: RecursionCycle> GlobalFixture<C> {
    pub fn cycle_name(&self) -> &'static str {
        C::name()
    }
}

pub type DefaultFixture = GlobalFixture<DefaultCycle>;
pub type MntFixture = GlobalFixture<Mnt4Mnt6Cycle>;

fn build_fixture_for_cycle<C: RecursionCycle>() -> GlobalFixture<C> {
    let mut rng = StdRng::seed_from_u64(999999);

    // Inner keys: AddCircuit on the inner curve
    let circuit_inner = AddCircuit {
        x: Some(InnerScalar::<C>::from(11u64)),
        y: Some(InnerScalar::<C>::from(4u64)),
        z: Some(InnerScalar::<C>::from(7u64)),
    };
    let (pk_inner, vk_inner) =
        Groth16::<C::InnerE>::circuit_specific_setup(circuit_inner, &mut rng).unwrap();

    // Outer keys: AddCircuit directly on the outer curve
    let circuit_outer = AddCircuit {
        x: Some(OuterScalar::<C>::from(11u64)),
        y: Some(OuterScalar::<C>::from(4u64)),
        z: Some(OuterScalar::<C>::from(7u64)),
    };
    let (pk_outer, vk_outer) =
        Groth16::<C::OuterE>::circuit_specific_setup(circuit_outer, &mut rng).unwrap();

    // Build PvugcVk from the outer proving key
    let pvugc_vk = crate::pvugc_outer::build_pvugc_vk_outer_from_pk_for::<C>(&pk_outer);

    // Outer-recursive keys: reuse setup_outer_params once per process
    let setup_start = Instant::now();
    let (pk_outer_recursive, vk_outer_recursive) =
        outer_compressed::setup_outer_params_for::<C>(&vk_inner, 1, &mut rng).unwrap();
    let outer_setup_time = setup_start.elapsed();
    eprintln!(
        "[fixture:{}] setup_outer_params (outer recursion) took {:?}",
        C::name(),
        outer_setup_time
    );
    let pvugc_vk_outer_recursive =
        crate::pvugc_outer::build_pvugc_vk_outer_from_pk_for::<C>(&pk_outer_recursive);

    GlobalFixture {
        pk_inner: Arc::new(pk_inner),
        vk_inner: Arc::new(vk_inner),
        pk_outer: Arc::new(pk_outer),
        vk_outer: Arc::new(vk_outer),
        pvugc_vk,
        pk_outer_recursive: Arc::new(pk_outer_recursive),
        vk_outer_recursive: Arc::new(vk_outer_recursive),
        pvugc_vk_outer_recursive,
        outer_setup_time,
    }
}

static GLOBAL_FIXTURE_DEFAULT: Lazy<Mutex<DefaultFixture>> =
    Lazy::new(|| Mutex::new(build_fixture_for_cycle::<DefaultCycle>()));

static GLOBAL_FIXTURE_MNT: Lazy<Mutex<MntFixture>> =
    Lazy::new(|| Mutex::new(build_fixture_for_cycle::<Mnt4Mnt6Cycle>()));

/// Get the global fixture for the default (BLS12/BW6) cycle
pub fn get_fixture() -> DefaultFixture {
    let guard = GLOBAL_FIXTURE_DEFAULT.lock().unwrap();
    guard.clone()
}

/// Get the global fixture for the MNT4/MNT6 experimental cycle
pub fn get_fixture_mnt() -> MntFixture {
    let guard = GLOBAL_FIXTURE_MNT.lock().unwrap();
    guard.clone()
}
