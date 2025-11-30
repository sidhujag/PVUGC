//! Global test fixtures with disk caching

use once_cell::sync::Lazy;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_groth16::{r1cs_to_qap::PvugcReduction, Groth16};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng; // Import AffineRepr for .zero()

use crate::outer_compressed::{
    self,
    cycles::{Bls12Bw6Cycle, Mnt4Mnt6Cycle},
    DefaultCycle, InnerScalar, OuterScalar, RecursionCycle,
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
    pub outer_setup_time: std::time::Duration,
}

impl<C: RecursionCycle> GlobalFixture<C> {
    pub fn cycle_name(&self) -> &'static str {
        C::name()
    }
}

pub type DefaultFixture = GlobalFixture<DefaultCycle>;
pub type BlsFixture = GlobalFixture<Bls12Bw6Cycle>;
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
    let (pk_outer, vk_outer) = Groth16::<C::OuterE, PvugcReduction>::circuit_specific_setup(
        circuit_outer,
        &mut rng,
    )
    .unwrap();

    // Build PvugcVk from the outer proving key (Manually, no baking for AddCircuit)
    // AddCircuit is used for basic tests, baking logic is specific to OuterCircuit
    use crate::ppe::PvugcVk;
    // With GT-Baking, we need PairingOutput elements instead of G1.
    // Since this is a dummy fixture for AddCircuit (which doesn't use baking), we can use identity in GT.
    use ark_ec::pairing::PairingOutput;
    use ark_ff::Field;
    
    let t_points_dummy =
        vec![PairingOutput(<<C::OuterE as Pairing>::TargetField as ark_ff::Field>::ONE); pk_outer.vk.gamma_abc_g1.len()];
    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        t_points_dummy,
    );

    // Outer-recursive keys: reuse setup_outer_params once per process
    let setup_start = Instant::now();
    let (pk_outer_recursive, vk_outer_recursive) =
        load_or_build_outer_recursive_crs::<C>(&vk_inner, 1);
    let outer_setup_time = setup_start.elapsed();
    eprintln!(
        "[fixture:{}] setup_outer_params (outer recursion) took {:?}",
        C::name(),
        outer_setup_time
    );

    GlobalFixture {
        pk_inner: Arc::new(pk_inner),
        vk_inner: Arc::new(vk_inner),
        pk_outer: Arc::new(pk_outer),
        vk_outer: Arc::new(vk_outer),
        pvugc_vk,
        pk_outer_recursive: Arc::new(pk_outer_recursive),
        vk_outer_recursive: Arc::new(vk_outer_recursive),
        outer_setup_time,
    }
}

fn load_or_build_outer_recursive_crs<C: RecursionCycle>(
    vk_inner: &ark_groth16::VerifyingKey<C::InnerE>,
    num_inputs: usize,
) -> (
    ark_groth16::ProvingKey<C::OuterE>,
    ark_groth16::VerifyingKey<C::OuterE>,
) {
    let safe_name = C::name().replace('/', "_").replace(' ', "_");
    let cache_path = format!("outer_crs_{}_{}.bin", safe_name, num_inputs);
    if Path::new(&cache_path).exists() {
        let file = File::open(&cache_path).expect("failed to open cached outer CRS");
        let reader = BufReader::new(file);
        return CanonicalDeserialize::deserialize_uncompressed(reader)
            .expect("failed to deserialize outer CRS");
    }

    let mut rng = StdRng::seed_from_u64(999999);
    let (pk, vk) =
        outer_compressed::setup_outer_params_for::<C>(vk_inner, num_inputs, &mut rng).unwrap();

    let file = File::create(&cache_path).expect("failed to create outer CRS cache file");
    let mut writer = BufWriter::new(file);
    (pk.clone(), vk.clone())
        .serialize_uncompressed(&mut writer)
        .expect("failed to serialize outer CRS");
    writer.flush().expect("failed to flush outer CRS cache");

    (pk, vk)
}

static GLOBAL_FIXTURE_DEFAULT: Lazy<Mutex<DefaultFixture>> =
    Lazy::new(|| Mutex::new(build_fixture_for_cycle::<DefaultCycle>()));

static GLOBAL_FIXTURE_BLS: Lazy<Mutex<BlsFixture>> =
    Lazy::new(|| Mutex::new(build_fixture_for_cycle::<Bls12Bw6Cycle>()));

static GLOBAL_FIXTURE_MNT: Lazy<Mutex<MntFixture>> =
    Lazy::new(|| Mutex::new(build_fixture_for_cycle::<Mnt4Mnt6Cycle>()));

/// Get the global fixture for the default (BLS12/BW6) cycle
pub fn get_fixture() -> DefaultFixture {
    let guard = GLOBAL_FIXTURE_DEFAULT.lock().unwrap();
    guard.clone()
}

pub fn get_fixture_bls() -> BlsFixture {
    let guard = GLOBAL_FIXTURE_BLS.lock().unwrap();
    guard.clone()
}

/// Get the global fixture for the MNT4/MNT6 experimental cycle
pub fn get_fixture_mnt() -> MntFixture {
    let guard = GLOBAL_FIXTURE_MNT.lock().unwrap();
    guard.clone()
}
