use std::{env, fs, io::Read, path::PathBuf};

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge as PoseidonSpongeNative},
    CryptographicSponge,
};
use ark_ec::AffineRepr;
use ark_groth16::r1cs_to_qap::LibsnarkReduction;
use ark_groth16::{Groth16, ProvingKey as Groth16ProvingKey, VerifyingKey as Groth16VerifyingKey};
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, uint8::UInt8};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::UniformRand;
use bitcoin::{secp256k1::SecretKey, Address, Network, PrivateKey};
use k256::elliptic_curve::{bigint::ArrayEncoding, ops::Reduce, Field};
use k256::{Scalar, U256};
use rand_core::OsRng;
use sha2::{Digest, Sha256}; // Added for .zero()

use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::poseidon_fr381_t3::{
    absorb_bytes_native_fr, absorb_bytes_var_fr, POSEIDON381_PARAMS_T3_V1,
};
use arkworks_groth16::ppe::PvugcVk;
use arkworks_groth16::{ColumnArms, OneSidedCommitments, OneSidedPvugc, SimpleCoeffRecorder};

const DEFAULT_PACKAGE_PATH: &str = "bounty_package.bin";

// === Shared helpers (mirroring tests/test_btc_kdf.rs) =======================

fn commitments_from_recorder(recorder: &SimpleCoeffRecorder<E>) -> OneSidedCommitments<E> {
    recorder.build_commitments()
}

/// Serialize bounty package (address, statement hash, proving key, column arms, ciphertexts, tags) to disk.
fn write_bounty_package(
    path: &PathBuf,
    addr: &Address,
    h: &Fr,
    pk: &Groth16ProvingKey<E>,
    shares: &[(ColumnArms<E>, Vec<u8>, [u8; 32])],
) {
    let mut buf = Vec::new();

    // Address
    let addr_string = addr.to_string();
    let addr_bytes = addr_string.as_bytes();
    (addr_bytes.len() as u32)
        .serialize_compressed(&mut buf)
        .expect("serialize addr len");
    buf.extend_from_slice(addr_bytes);

    // Statement hash h
    h.serialize_compressed(&mut buf)
        .expect("serialize statement hash");

    // Proving key (CRS) for Groth16, used at decap-time
    pk.serialize_compressed(&mut buf)
        .expect("serialize proving key");

    // Shares: ColumnArms + τ_i tag + ciphertext
    (shares.len() as u32)
        .serialize_compressed(&mut buf)
        .expect("serialize shares len");
    for (arms, ct, tau) in shares {
        arms.serialize_compressed(&mut buf).expect("serialize arms");
        // τ_i tag (fixed 32 bytes)
        buf.extend_from_slice(tau);
        (ct.len() as u32)
            .serialize_compressed(&mut buf)
            .expect("serialize ct len");
        buf.extend_from_slice(ct);
    }

    fs::write(path, buf).expect("write bounty package");
}

/// Deserialize bounty package from disk.
fn read_bounty_package(
    path: &PathBuf,
) -> (
    String,
    Fr,
    Groth16ProvingKey<E>,
    Vec<(ColumnArms<E>, Vec<u8>, [u8; 32])>,
) {
    let data = fs::read(path).expect("read bounty package");
    let mut cursor: &[u8] = &data;

    // Address
    let addr_len: u32 =
        CanonicalDeserialize::deserialize_compressed(&mut cursor).expect("addr len");
    let mut addr_bytes = vec![0u8; addr_len as usize];
    cursor.read_exact(&mut addr_bytes).expect("addr bytes");
    let addr_str = String::from_utf8(addr_bytes).expect("addr utf8");

    // Statement hash h
    let h = Fr::deserialize_compressed(&mut cursor).expect("hash");

    // Proving key (CRS) for Groth16
    let pk = Groth16ProvingKey::<E>::deserialize_compressed(&mut cursor).expect("pk");

    // Shares
    let shares_len: u32 =
        CanonicalDeserialize::deserialize_compressed(&mut cursor).expect("shares_len");
    let mut shares = Vec::with_capacity(shares_len as usize);
    for _ in 0..shares_len {
        let arms = ColumnArms::<E>::deserialize_compressed(&mut cursor).expect("arms");
        // τ_i tag (fixed 32 bytes)
        let mut tau = [0u8; 32];
        cursor.read_exact(&mut tau).expect("tau bytes");
        let ct_len: u32 =
            CanonicalDeserialize::deserialize_compressed(&mut cursor).expect("ct_len");
        let mut ct = vec![0u8; ct_len as usize];
        cursor.read_exact(&mut ct).expect("ct bytes");
        shares.push((arms, ct, tau));
    }

    (addr_str, h, pk, shares)
}

/// Build AD_core bytes for bounty DEM binding.
/// Binds vk, statement hash, share index, and ColumnArms to the ciphertext.
fn build_bounty_ad_core(
    vk: &Groth16VerifyingKey<E>,
    h: &Fr,
    share_index: u32,
    col_arms: &ColumnArms<E>,
) -> Vec<u8> {
    // Domain separation for bounty profile
    const PROFILE: &[u8] = b"PVUGC/BOUNTY/v1";

    // vk hash
    let mut vk_bytes = Vec::new();
    vk.serialize_compressed(&mut vk_bytes)
        .expect("serialize vk");
    let mut hasher = Sha256::new();
    hasher.update(&vk_bytes);
    let vk_hash: [u8; 32] = hasher.finalize().into();

    // statement hash h bytes + hash
    let mut h_bytes = Vec::new();
    h.serialize_compressed(&mut h_bytes)
        .expect("serialize statement hash");
    let mut hasher_h = Sha256::new();
    hasher_h.update(&h_bytes);
    let h_hash: [u8; 32] = hasher_h.finalize().into();

    // ColumnArms serialization
    let mut arms_bytes = Vec::new();
    col_arms
        .serialize_compressed(&mut arms_bytes)
        .expect("serialize column arms");

    // Assemble AD_core
    let mut ad_core = Vec::new();
    ad_core.extend_from_slice(PROFILE);
    ad_core.extend_from_slice(&vk_hash);
    ad_core.extend_from_slice(&h_hash);
    ad_core.extend_from_slice(&share_index.to_le_bytes());
    ad_core.extend_from_slice(&arms_bytes);

    ad_core
}

/// Preimage circuit: proves that `expected_hash` is the Poseidon hash
/// of (domain || passphrase || ctx), without revealing the passphrase.
#[derive(Clone)]
struct PreimageCircuit {
    pub expected_hash: Option<Fr>,
    pub passphrase: Option<Vec<u8>>,
    pub ctx: Vec<u8>,
}

impl ConstraintSynthesizer<Fr> for PreimageCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Public input: expected Poseidon hash
        let hash_var = FpVar::new_input(cs.clone(), || {
            self.expected_hash.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Witness: passphrase bytes
        let pass_bytes = self
            .passphrase
            .clone()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let pass_vars = UInt8::new_witness_vec(cs.clone(), &pass_bytes)?;

        // Constants: domain and context bytes
        let domain_bytes: Vec<UInt8<Fr>> = b"PVUGC/PREIMAGE"
            .iter()
            .map(|b| UInt8::constant(*b))
            .collect();
        let ctx_bytes: Vec<UInt8<Fr>> = self.ctx.iter().map(|b| UInt8::constant(*b)).collect();

        // Poseidon hash inside the circuit
        let mut sponge = PoseidonSpongeVar::new(cs.clone(), &POSEIDON381_PARAMS_T3_V1);
        absorb_bytes_var_fr(&mut sponge, &domain_bytes)?;
        absorb_bytes_var_fr(&mut sponge, &pass_vars)?;
        absorb_bytes_var_fr(&mut sponge, &ctx_bytes)?;
        let hash_computed = sponge.squeeze_field_elements(1)?[0].clone();

        hash_var.enforce_equal(&hash_computed)?;
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

// === CLI operations =========================================================

fn arm(passphrase: &str, ctx: &str, path: PathBuf) {
    // Host-side Poseidon hash h = Poseidon(domain || passphrase || ctx)
    let pass_bytes = passphrase.as_bytes();
    let ctx_bytes = ctx.as_bytes();

    let mut sponge = PoseidonSpongeNative::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
    absorb_bytes_native_fr(&mut sponge, b"PVUGC/PREIMAGE");
    absorb_bytes_native_fr(&mut sponge, pass_bytes);
    absorb_bytes_native_fr(&mut sponge, ctx_bytes);
    let h = sponge.squeeze_field_elements(1)[0];

    // Groth16 setup for this statement (circuit-specific CRS).
    // The CRS (proving key) is serialized into the bounty package; no seed is stored.
    // SECURITY NOTE: In production PVUGC, the CRS MUST be "Lean" (i.e., stripped of raw Powers of Tau).
    // Publishing raw generic PoT along with the witness masks allows a "Full Span" attack.
    // Here, circuit_specific_setup produces a specific PK, but ensure the distribution does not leak PoT.
    let circuit = PreimageCircuit {
        expected_hash: Some(h),
        passphrase: Some(pass_bytes.to_vec()),
        ctx: ctx_bytes.to_vec(),
    };
    let mut os_rng = OsRng;
    let (pk, vk) =
        Groth16::<E, LibsnarkReduction>::circuit_specific_setup(circuit, &mut os_rng).unwrap();
    // Use pairing::Pairing trait to access G1Affine type
    use ark_ec::pairing::Pairing;
    use ark_ec::pairing::PairingOutput;
    use ark_ff::{Field, One};
    let q_dummy = vec![PairingOutput(<<E as Pairing>::TargetField as Field>::ONE); vk.gamma_abc_g1.len()];
    let alpha_g1_beta_g2 = E::pairing(vk.alpha_g1, vk.beta_g2);
    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        vk.beta_g2,
        vk.delta_g2,
        pk.b_g2_query.clone(),
        q_dummy,
        alpha_g1_beta_g2,
    );

    let statement_x = vec![h];

    // Sample a random adaptor/BTC secret alpha and split into 2 shares.
    // This uses OS randomness only and is *not* reproducible from the public seed.
    let alpha_scalar = Scalar::random(&mut os_rng);
    let share1 = Scalar::random(&mut os_rng);
    let share2 = alpha_scalar - share1;

    // Derive and print the bounty Bitcoin address from alpha (for funding)
    let alpha_bytes = alpha_scalar.to_bytes();
    let btc_sk =
        SecretKey::from_slice(&alpha_bytes).expect("alpha_bytes must be a valid secp256k1 key");
    let secp = bitcoin::secp256k1::Secp256k1::new();
    let privkey = PrivateKey::new(btc_sk, Network::Testnet);
    let pk_btc = privkey.public_key(&secp);
    let bounty_addr =
        Address::p2wpkh(&pk_btc, Network::Testnet).expect("P2WPKH address derivation must succeed");
    println!("ARM: bounty address (Testnet P2WPKH): {}", bounty_addr);

    // Two independent armers with random rho; both rely on the same statement.
    // rho is also drawn from OS randomness so it cannot be reconstructed from the seed.
    let mut shares = Vec::new();
    for (idx, share_scalar) in [share1, share2].into_iter().enumerate() {
        let rho = Fr::rand(&mut os_rng);
        let (_bases, col_arms, _r, k) =
            OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &statement_x, &rho).unwrap();

        let share_bytes = share_scalar.to_bytes().to_vec();
        // Build AD_core binding this share to vk, statement, and ColumnArms
        let ad_core = build_bounty_ad_core(&vk, &h, idx as u32, &col_arms);
        // Encrypt share with key-committing DEM and compute τ_i tag
        let ciphertext =
            OneSidedPvugc::encrypt_with_key_dem::<E>(&k, &ad_core, &share_bytes).unwrap();
        let tau = OneSidedPvugc::compute_key_commitment_tag_dem::<E>(&k, &ad_core, &ciphertext);

        shares.push((col_arms, ciphertext, tau));
    }

    write_bounty_package(&path, &bounty_addr, &h, &pk, &shares);
    println!("ARM: wrote bounty package to {}", path.display());
}

fn decap(passphrase: &str, ctx: &str, path: PathBuf) {
    let pass_bytes = passphrase.as_bytes();
    let ctx_bytes = ctx.as_bytes();

    // Recompute statement hash h from passphrase and context
    let mut sponge = PoseidonSpongeNative::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
    absorb_bytes_native_fr(&mut sponge, b"PVUGC/PREIMAGE");
    absorb_bytes_native_fr(&mut sponge, pass_bytes);
    absorb_bytes_native_fr(&mut sponge, ctx_bytes);
    let h = sponge.squeeze_field_elements(1)[0];

    // Read bounty package from disk
    let (addr_str, h_pkg, pk, shares) = read_bounty_package(&path);
    let vk = pk.vk.clone();
    println!("DECAP: package address {}", addr_str);

    if h_pkg != h {
        eprintln!("DECAP: statement hash mismatch (wrong passphrase or ctx)");
        std::process::exit(1);
    }

    // Build preimage circuit and prove through Groth16 to gate decap
    let circuit = PreimageCircuit {
        expected_hash: Some(h_pkg),
        passphrase: Some(pass_bytes.to_vec()),
        ctx: ctx_bytes.to_vec(),
    };

    let mut rng = OsRng;
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    recorder.set_num_instance_variables(vk.gamma_abc_g1.len());
    let proof =
        Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut recorder).unwrap();
    let ok = Groth16::<E, LibsnarkReduction>::verify(&vk, &[h_pkg], &proof).unwrap();
    if !ok {
        eprintln!("DECAP: Groth16 preimage proof verification failed");
        std::process::exit(1);
    }
    let commitments = commitments_from_recorder(&recorder);

    // Decap: derive each K via OneSidedPvugc::decapsulate and recover the shares
    let mut recovered = Scalar::ZERO;
    for (idx, (col_arms, ciphertext, tau)) in shares.iter().enumerate() {
        let k_dec = OneSidedPvugc::decapsulate(&commitments, col_arms).expect("decap");
        // Rebuild AD_core for this share
        let ad_core = build_bounty_ad_core(&vk, &h_pkg, idx as u32, col_arms);

        // Verify key-commitment tag before decryption
        let tau_arr: [u8; 32] = *tau;
        let key_commit_ok =
            OneSidedPvugc::verify_key_commitment_dem::<E>(&k_dec, &ad_core, ciphertext, &tau_arr);
        if !key_commit_ok {
            eprintln!("DECAP: key-commitment tag mismatch for share {}", idx);
            std::process::exit(1);
        }

        // Decrypt with DEM-Poseidon using the same AD_core
        let plain = OneSidedPvugc::decrypt_with_key_dem::<E>(&k_dec, &ad_core, ciphertext)
            .expect("decrypt share");
        if plain.len() != 32 {
            eprintln!("DECAP: invalid share length for share {}", idx);
            std::process::exit(1);
        }
        let mut share_bytes = [0u8; 32];
        share_bytes.copy_from_slice(&plain);
        let share_scalar = Scalar::reduce(U256::from_be_byte_array(share_bytes.into()));
        recovered += share_scalar;
    }

    // Derive and print the BTC key/address from the decapped secret
    let recovered_bytes = recovered.to_bytes();
    let btc_sk =
        SecretKey::from_slice(&recovered_bytes).expect("recovered_bytes must be a valid key");
    let secp = bitcoin::secp256k1::Secp256k1::new();
    let privkey = PrivateKey::new(btc_sk, Network::Testnet);
    let pk_btc = privkey.public_key(&secp);
    let addr =
        Address::p2wpkh(&pk_btc, Network::Testnet).expect("P2WPKH address derivation must succeed");
    println!("DECAP: recovered address (Testnet P2WPKH): {}", addr);
    println!("DECAP: recovered private key (WIF): {}", privkey.to_wif());

    if addr_str != addr.to_string() {
        eprintln!("DECAP: address mismatch against package");
        std::process::exit(1);
    }
}

fn usage() {
    eprintln!("pvugc-bounty CLI");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  pvugc-bounty arm <passphrase> [ctx] [package_path]");
    eprintln!("  pvugc-bounty decap <passphrase> [ctx] [package_path]");
    eprintln!();
    eprintln!("Defaults:");
    eprintln!("  ctx           = \"pvugc-bounty-context\"");
    eprintln!("  package_path  = \"{}\"", DEFAULT_PACKAGE_PATH);
}

fn main() {
    let mut args = env::args().skip(1);
    let cmd = match args.next() {
        Some(c) => c,
        None => {
            usage();
            std::process::exit(1);
        }
    };

    let passphrase = match args.next() {
        Some(p) => p,
        None => {
            usage();
            std::process::exit(1);
        }
    };

    let ctx = args
        .next()
        .unwrap_or_else(|| "pvugc-bounty-context".to_string());
    let path = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_PACKAGE_PATH));

    match cmd.as_str() {
        "arm" => arm(&passphrase, &ctx, path),
        "decap" => decap(&passphrase, &ctx, path),
        _ => {
            usage();
            std::process::exit(1);
        }
    }
}
