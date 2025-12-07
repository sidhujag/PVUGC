#![cfg(test)]

use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
    path::Path,
    sync::{Arc, Mutex},
};

use ark_bls12_377::Bls12_377;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use once_cell::sync::Lazy;
use winter_crypto::hashers::Rp64_256;
use winter_crypto::{DefaultRandomCoin, MerkleTree};
use winter_math::fields::f64::BaseElement;
use winterfell::{Air, Proof, Trace};

use super::stark_proof_parser::{
    derive_query_positions, parse_proof_for_circuit_with_query_positions,
};
use super::tests::helpers::cubic_fib::{generate_test_cubic_fib_proof_rpo, CubicFibAir};
use super::tests::helpers::simple_vdf::{generate_test_vdf_proof_rpo, VdfAir};
use super::{AirParams, FullStarkVerifierCircuit, StarkInnerFr};
use crate::stark::gadgets::fri::FriTerminalKind;
use crate::stark::gadgets::utils::CombinerKind;
use ark_snark::SNARK;

const INNER_CRS_CACHE: &str = "inner_crs_pk_vk.bin";
static INNER_CRS_KEYS: Lazy<
    Mutex<Option<(Arc<ProvingKey<Bls12_377>>, Arc<VerifyingKey<Bls12_377>>)>>,
> = Lazy::new(|| Mutex::new(None));

/// Load the Groth16 proving/verifying keys for the Full STARK verifier circuit, caching them on disk.
pub fn get_or_init_inner_crs_keys() -> (Arc<ProvingKey<Bls12_377>>, Arc<VerifyingKey<Bls12_377>>) {
    let mut guard = INNER_CRS_KEYS.lock().unwrap();
    if let Some((pk, vk)) = guard.as_ref() {
        return (Arc::clone(pk), Arc::clone(vk));
    }

    let (pk, vk) = load_or_build_inner_crs_keys();
    let pk_arc = Arc::new(pk);
    let vk_arc = Arc::new(vk);
    *guard = Some((Arc::clone(&pk_arc), Arc::clone(&vk_arc)));
    (pk_arc, vk_arc)
}

fn load_or_build_inner_crs_keys() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
    if Path::new(INNER_CRS_CACHE).exists() {
        let file = File::open(INNER_CRS_CACHE).expect("failed to open cached inner CRS keys");
        let reader = BufReader::new(file);
        let (pk, vk): (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) =
            CanonicalDeserialize::deserialize_uncompressed(reader)
                .expect("failed to deserialize inner CRS keys");
        return (pk, vk);
    }

    let instance = build_vdf_stark_instance(3, 8);
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) =
        Groth16::<Bls12_377>::circuit_specific_setup(instance.circuit.clone(), &mut rng).unwrap();

    let file = File::create(INNER_CRS_CACHE).expect("failed to create inner CRS cache file");
    let mut writer = BufWriter::new(file);
    let serialized = (pk.clone(), vk.clone());
    serialized
        .serialize_uncompressed(&mut writer)
        .expect("failed to serialize STARK SNARK keys");
    writer.flush().expect("failed to flush STARK SNARK cache");

    (pk, vk)
}

/// Convenience wrapper that packages a Winterfell VDF proof into a Groth16-ready circuit.
#[derive(Clone)]
pub struct VdfStarkInstance {
    pub circuit: FullStarkVerifierCircuit,
    pub statement_hash: StarkInnerFr,
}

impl VdfStarkInstance {
    pub fn statement(&self) -> StarkInnerFr {
        self.statement_hash
    }
}

pub fn build_vdf_stark_instance(start_value: u64, steps: usize) -> VdfStarkInstance {
    let start = BaseElement::new(start_value);
    let (proof, trace) = generate_test_vdf_proof_rpo(start, steps);
    build_instance_from_proof::<VdfAir>(proof, trace)
}

pub fn build_cubic_fib_stark_instance(start_a: u64, start_b: u64, steps: usize) -> VdfStarkInstance {
    let a = BaseElement::new(start_a);
    let b = BaseElement::new(start_b);
    let (proof, trace) = generate_test_cubic_fib_proof_rpo(a, b, steps);
    build_instance_from_proof::<CubicFibAir>(proof, trace)
}

fn build_instance_from_proof<A>(
    proof: Proof,
    trace: winterfell::TraceTable<BaseElement>,
) -> VdfStarkInstance
where
    A: Air<BaseField = BaseElement, PublicInputs = BaseElement>,
{
    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof.options().num_queries();
    let trace_width = proof.context.trace_info().main_trace_width();

    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    let pub_inputs_fe = BaseElement::new(pub_inputs_u64[0]);
    let air = A::new(
        proof.context.trace_info().clone(),
        pub_inputs_fe,
        proof.options().clone(),
    );

    let lde_generator_from_air = air.lde_domain_generator().as_int();
    let domain_offset_from_air = air.domain_offset().as_int();
    let g_trace_from_air = air.trace_domain_generator().as_int();

    let coeffs_len = proof
        .fri_proof
        .clone()
        .parse_remainder::<BaseElement>()
        .map(|v: Vec<BaseElement>| v.len())
        .unwrap_or(0);
    let fri_terminal = if coeffs_len == 0 {
        FriTerminalKind::Constant
    } else {
        FriTerminalKind::Poly {
            degree: coeffs_len - 1,
        }
    };

    let air_params = AirParams {
        trace_width,
        comp_width: air.context().num_constraint_composition_columns(),
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers: proof
            .options()
            .to_fri_options()
            .num_fri_layers(lde_domain_size),
        lde_generator: lde_generator_from_air,
        domain_offset: domain_offset_from_air,
        g_lde: lde_generator_from_air,
        g_trace: g_trace_from_air,
        combiner_kind: CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: proof.context.num_constraints(),
        grinding_factor: proof.options().grinding_factor(),
    };

    let acceptable_options =
        winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);
    winterfell::verify::<A, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        proof.clone(),
        pub_inputs_fe,
        &acceptable_options,
    )
    .expect("Winterfell verification failed");

    let query_positions = derive_query_positions::<Rp64_256, _>(&proof, &air, &pub_inputs_fe);

    let circuit = parse_proof_for_circuit_with_query_positions::<Rp64_256, MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );

    VdfStarkInstance {
        statement_hash: circuit.statement_hash,
        circuit,
    }
}
