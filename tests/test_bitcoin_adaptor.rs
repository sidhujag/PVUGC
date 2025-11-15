//! End-to-end integration test demonstrating a trustless Bitcoin adaptor
//! signature pipeline backed by PVUGC. The test models the full lifecycle
//! expected on mainnet:
//!
//! Phase A (pre-arming):
//!   * all operators pre-arm PVUGC, encrypt their adaptor shares, build an
//!     N-of-N DepositPackage, and publish an aggregated MuSig adaptor
//!     pre-signature for a frozen Taproot SIGHASH.
//!
//! Phase B (deposit):
//!   * the depositor sends funds to the registered Taproot output key and a
//!     policy check rejects deposits that are not tied to the published
//!     package.
//!
//! Phase C (unlock):
//!   * a valid Groth16 proof allows any party to decapsulate every armer's
//!     ciphertext, recover the adaptor secret, finish the signature using the
//!     pre-published pre-signature, and extract the adaptor secret from the
//!     final signature.
//!
//! The test also exercises adversarial scenarios: missing shares block
//! completion, tampering with the ciphertext is detected by the PoCE-B key
//! commitment, and proofs for different statements yield unrelated keys and
//! therefore cannot complete the spend.

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup; // for into_affine()
use ark_ec::PrimeGroup; // for G1::generator()
use ark_groth16::Groth16;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use ark_std::{rand::rngs::StdRng, rand::SeedableRng, UniformRand};

use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ct::{serialize_gt, AdCore, DemP2};
use arkworks_groth16::ppe::PvugcVk;
use arkworks_groth16::{OneSidedCommitments, OneSidedPvugc, PvugcBundle};

use arkworks_groth16::bitcoin::{
    bip340_challenge, encoded_x, signature_bytes, tagged_hash, verify_schnorr_signature, y_is_even,
};

use bitcoin::absolute::LockTime;
use bitcoin::amount::Amount;
use bitcoin::hashes::Hash;
use bitcoin::opcodes::all::OP_PUSHNUM_1;
use bitcoin::script::Builder;
use bitcoin::sighash::{Prevouts, SighashCache, TapSighashType};
use bitcoin::transaction::Version;
use bitcoin::{OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid, Witness};

use k256::elliptic_curve::bigint::ArrayEncoding;
use k256::elliptic_curve::ff::Field;
use k256::elliptic_curve::group::prime::PrimeCurveAffine;
use k256::elliptic_curve::group::Group;
use k256::elliptic_curve::ops::Reduce;
use k256::elliptic_curve::PrimeField;
use k256::{AffinePoint, FieldBytes, ProjectivePoint, Scalar, U256};

use sha2::{Digest, Sha256};

type E = Bls12_381;

/// Simple quadratic circuit: asserts x = y^2
#[derive(Clone)]
struct SquareCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SquareCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

#[derive(Clone)]
struct Participant {
    secret: Scalar,
    public: ProjectivePoint,
}

impl Participant {
    fn random(rng: &mut StdRng) -> Self {
        loop {
            let secret = Scalar::random(&mut *rng);
            if bool::from(secret.is_zero()) {
                continue;
            }
            let public = ProjectivePoint::GENERATOR * secret;
            return Self { secret, public };
        }
    }

    fn affine(&self) -> AffinePoint {
        AffinePoint::from(self.public)
    }
}

#[derive(Clone)]
struct Nonce {
    secret: Scalar,
    public: ProjectivePoint,
}

impl Nonce {
    fn random(rng: &mut StdRng) -> Self {
        let secret = Scalar::random(rng);
        let public = ProjectivePoint::GENERATOR * secret;
        Self { secret, public }
    }
}

#[derive(Clone)]
struct AntiReplay {
    expiry_height: u64,
    fee_rate_sats_per_vb: u64,
    cpfp_anchor_value: u64,
}

impl AntiReplay {
    fn to_bytes(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[..8].copy_from_slice(&self.expiry_height.to_le_bytes());
        out[8..16].copy_from_slice(&self.fee_rate_sats_per_vb.to_le_bytes());
        out[16..24].copy_from_slice(&self.cpfp_anchor_value.to_le_bytes());
        out
    }
}

struct BridgeContext {
    network: &'static str,
    instance: &'static str,
    anti_replay: AntiReplay,
}

impl BridgeContext {
    fn context_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(self.network.as_bytes());
        hasher.update(self.instance.as_bytes());
        hasher.update(&self.anti_replay.to_bytes());
        let digest = hasher.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(&digest);
        out
    }

    fn gs_digest(&self, adaptor_x: &[u8; 32], adaptor_y_is_even: bool) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&self.context_hash());
        hasher.update(adaptor_x);
        hasher.update(&[adaptor_y_is_even as u8]);
        let digest = hasher.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(&digest);
        out
    }
}

#[derive(Clone)]
struct EncryptedShare {
    ciphertext: Vec<u8>,
    tau: Vec<u8>,
}

#[derive(Clone)]
struct OperatorArming<Ep: Pairing> {
    participant: Participant,
    adaptor_share: Scalar,
    adaptor_commitment: AffinePoint,
    column_arms: arkworks_groth16::arming::ColumnArms<Ep>,
    encrypted_share: EncryptedShare,
    expected_key: ark_ec::pairing::PairingOutput<Ep>,
}

#[derive(Clone)]
struct ArmerPublicPackage<Ep: Pairing> {
    pubkey_x: [u8; 32],
    adaptor_commitment_x: [u8; 32],
    column_arms: arkworks_groth16::arming::ColumnArms<Ep>,
    encrypted_share: EncryptedShare,
}

#[derive(Clone)]
struct DepositPackage<Ep: Pairing> {
    ctx_hash: [u8; 32],
    gs_digest: [u8; 32],
    output_key_x: [u8; 32],
    adaptor_point_x: [u8; 32],
    adaptor_y_is_even: bool,
    musig_l: [u8; 32],
    anti_replay: AntiReplay,
    armers: Vec<ArmerPublicPackage<Ep>>,
}

impl<Ep: Pairing> DepositPackage<Ep> {
    fn hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&self.ctx_hash);
        hasher.update(&self.gs_digest);
        hasher.update(&self.output_key_x);
        hasher.update(&self.adaptor_point_x);
        hasher.update(&[self.adaptor_y_is_even as u8]);
        hasher.update(&self.musig_l);
        hasher.update(&self.anti_replay.to_bytes());

        for armer in &self.armers {
            hasher.update(&armer.pubkey_x);
            hasher.update(&armer.adaptor_commitment_x);
            let mut buf = Vec::new();
            armer
                .column_arms
                .serialize_compressed(&mut buf)
                .expect("serialize column arms");
            hasher.update(&buf);
            hasher.update(&(armer.encrypted_share.ciphertext.len() as u64).to_le_bytes());
            hasher.update(&armer.encrypted_share.ciphertext);
            hasher.update(&(armer.encrypted_share.tau.len() as u64).to_le_bytes());
            hasher.update(&armer.encrypted_share.tau);
        }

        let digest = hasher.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(&digest);
        out
    }
}

struct PreSignaturePackage {
    aggregated_nonce: AffinePoint,
    s_prime: Scalar,
    message: [u8; 32],
    nonce_negated: bool,
    signer_set: Vec<[u8; 32]>,
    musig_l: [u8; 32],
    output_key_x: [u8; 32],
    adaptor_point_x: [u8; 32],
    adaptor_y_is_even: bool,
}

impl PreSignaturePackage {
    fn hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&encoded_x(&self.aggregated_nonce));
        hasher.update(&scalar_to_bytes(&self.s_prime));
        hasher.update(&self.message);
        hasher.update(&[self.nonce_negated as u8]);
        hasher.update(&self.musig_l);
        hasher.update(&self.output_key_x);
        hasher.update(&self.adaptor_point_x);
        hasher.update(&[self.adaptor_y_is_even as u8]);
        for pk in &self.signer_set {
            hasher.update(pk);
        }
        let digest = hasher.finalize();
        let mut out = [0u8; 32];
        out.copy_from_slice(&digest);
        out
    }
}

struct ReadyAttestation {
    message: [u8; 32],
    signatures: Vec<[u8; 64]>,
}

impl ReadyAttestation {
    fn sign(participants: &[Participant], message: [u8; 32], rng: &mut StdRng) -> Self {
        let signatures = participants
            .iter()
            .map(|p| bip340_single_sign(p, &message, rng))
            .collect();
        Self {
            message,
            signatures,
        }
    }

    fn verify(&self, participants: &[Participant]) -> bool {
        if self.signatures.len() != participants.len() {
            return false;
        }
        participants
            .iter()
            .zip(self.signatures.iter())
            .all(|(participant, sig)| {
                let affine = participant.affine();
                verify_schnorr_signature(&affine, &self.message, sig)
            })
    }
}

fn affine_from_projective(point: &ProjectivePoint) -> AffinePoint {
    AffinePoint::from(*point)
}

// Using helpers from arkworks_groth16::bitcoin

fn scalar_from_bytes(bytes: &[u8; 32]) -> Scalar {
    Scalar::reduce(U256::from_be_byte_array((*bytes).into()))
}

fn scalar_from_bytes_strict(bytes: &[u8; 32]) -> Scalar {
    Scalar::from_repr(FieldBytes::from(*bytes)).expect("non-canonical scalar encoding")
}

fn scalar_to_bytes(s: &Scalar) -> [u8; 32] {
    let field_bytes = s.to_bytes();
    let mut out = [0u8; 32];
    out.copy_from_slice(&field_bytes);
    out
}

fn neg_scalar(s: &Scalar) -> Scalar {
    -*s
}

fn musig_coefficients(participants: &[Participant]) -> (Vec<Scalar>, AffinePoint, [u8; 32]) {
    assert!(!participants.is_empty());
    let mut l_hasher = Sha256::new();
    for participant in participants {
        let affine = participant.affine();
        l_hasher.update(encoded_x(&affine));
    }
    let l = l_hasher.finalize();
    let mut l_bytes = [0u8; 32];
    l_bytes.copy_from_slice(&l);

    let mut coeffs = Vec::with_capacity(participants.len());
    let mut agg = ProjectivePoint::IDENTITY;

    for participant in participants {
        let affine = participant.affine();
        let mut hasher = Sha256::new();
        hasher.update(&l_bytes);
        hasher.update(encoded_x(&affine));
        let coeff_bytes = hasher.finalize();
        let mut coeff_arr = [0u8; 32];
        coeff_arr.copy_from_slice(&coeff_bytes);
        let coeff = scalar_from_bytes(&coeff_arr);
        coeffs.push(coeff);
        agg += participant.public * coeff;
    }

    let mut agg_affine = affine_from_projective(&agg);
    if !y_is_even(&agg_affine) {
        agg = -agg;
        agg_affine = affine_from_projective(&agg);
        for coeff in &mut coeffs {
            *coeff = neg_scalar(coeff);
        }
    }

    debug_assert!(y_is_even(&agg_affine));

    (coeffs, agg_affine, l_bytes)
}

fn musig_list_hash_from_pubkeys(pk_x_list: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for pk_x in pk_x_list {
        hasher.update(pk_x);
    }
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn aggregate_nonces(nonces: &[Nonce]) -> (AffinePoint, bool) {
    let mut agg = ProjectivePoint::IDENTITY;
    for nonce in nonces {
        agg += nonce.public;
    }
    let mut agg_affine = affine_from_projective(&agg);
    let mut negated = false;
    if !y_is_even(&agg_affine) {
        agg = -agg;
        agg_affine = affine_from_projective(&agg);
        negated = true;
    }
    (agg_affine, negated)
}

// Using helpers from arkworks_groth16::bitcoin

fn taproot_key_spend_sighash(tx: &Transaction, prevouts: &[TxOut]) -> [u8; 32] {
    let mut cache = SighashCache::new(tx);
    let sighash = cache
        .taproot_key_spend_signature_hash(0, &Prevouts::All(prevouts), TapSighashType::All)
        .expect("sighash");
    let mut out = [0u8; 32];
    out.copy_from_slice(sighash.as_ref());
    out
}

fn taproot_tweak_scalar(internal_key: &AffinePoint, merkle_root: Option<[u8; 32]>) -> Scalar {
    let mut tweak_input = Vec::with_capacity(32 + if merkle_root.is_some() { 32 } else { 0 });
    tweak_input.extend_from_slice(&encoded_x(internal_key));
    if let Some(root) = merkle_root {
        tweak_input.extend_from_slice(&root);
    }
    let tweak_hash = tagged_hash("TapTweak", &tweak_input);
    scalar_from_bytes(&tweak_hash)
}

fn taproot_output_key(internal_key: &AffinePoint, merkle_root: Option<[u8; 32]>) -> AffinePoint {
    let tweak = taproot_tweak_scalar(internal_key, merkle_root);
    let tweaked = ProjectivePoint::from(*internal_key) + ProjectivePoint::GENERATOR * tweak;
    let tweaked_affine = affine_from_projective(&tweaked);
    assert!(
        !bool::from(tweaked_affine.is_identity()),
        "taproot output key must not be the identity"
    );
    tweaked_affine
}

fn build_p2tr_script(output_key: &AffinePoint) -> ScriptBuf {
    Builder::new()
        .push_opcode(OP_PUSHNUM_1)
        .push_slice(&encoded_x(output_key))
        .into_script()
}

fn assemble_withdrawal_transaction(
    deposit_outpoint: OutPoint,
    deposit_prevout: TxOut,
    withdraw_value: Amount,
    recipient_script: ScriptBuf,
    cpfp_anchor_script: ScriptBuf,
    cpfp_value: Amount,
) -> (Transaction, Vec<TxOut>) {
    let tx = Transaction {
        version: Version::TWO,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: deposit_outpoint,
            script_sig: ScriptBuf::new(),
            sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
            witness: Witness::new(),
        }],
        output: vec![
            TxOut {
                value: withdraw_value,
                script_pubkey: recipient_script,
            },
            TxOut {
                value: cpfp_value,
                script_pubkey: cpfp_anchor_script,
            },
        ],
    };
    (tx, vec![deposit_prevout])
}

#[test]
fn test_pvugc_bitcoin_adaptor_end_to_end() {
    let mut rng = StdRng::seed_from_u64(1337);

    // === Proving system setup ===
    let public_input = Fr::from(25u64);
    let statement_x = vec![public_input];
    let witness = Fr::from(5u64);
    let circuit = SquareCircuit {
        x: Some(public_input),
        y: Some(witness),
    };

    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Shared column bases for PoCE-A attest/verify
    let bases = OneSidedPvugc::build_column_bases(&pvugc_vk, &vk, &statement_x).expect("bases");

    // === Phase A: pre-arming and registration ===
    let bridge_context = BridgeContext {
        network: "signet",
        instance: "pvugc-bridge-instance",
        anti_replay: AntiReplay {
            expiry_height: 1_000_000,
            fee_rate_sats_per_vb: 2,
            cpfp_anchor_value: 3_000,
        },
    };

    let mut participants = vec![
        Participant::random(&mut rng),
        Participant::random(&mut rng),
        Participant::random(&mut rng),
    ];
    participants.sort_by(|a, b| encoded_x(&a.affine()).cmp(&encoded_x(&b.affine())));
    let (coefficients, aggregated_key, musig_l) = musig_coefficients(&participants);

    // Sample adaptor shares and commitments
    let mut operator_armings = Vec::new();
    let mut rhos: Vec<Fr> = Vec::new();
    let mut adaptor_sum = ProjectivePoint::IDENTITY;
    for participant in &participants {
        let share = loop {
            let candidate = Scalar::random(&mut rng);
            if bool::from(candidate.is_zero()) {
                continue;
            }
            break candidate;
        };
        let commitment = ProjectivePoint::GENERATOR * share;
        assert!(
            !bool::from(commitment.is_identity()),
            "adaptor commitment must not be the identity"
        );
        adaptor_sum += commitment;

        let rho = Fr::rand(&mut rng);
        rhos.push(rho);
        let (_bases, col_arms, _r, expected_key) =
            OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &statement_x, &rho).unwrap();

        operator_armings.push(OperatorArming {
            participant: participant.clone(),
            adaptor_share: share,
            adaptor_commitment: affine_from_projective(&commitment),
            column_arms: col_arms.clone(),
            encrypted_share: EncryptedShare {
                ciphertext: Vec::new(),
                tau: Vec::new(),
            },
            expected_key,
        });
    }

    let adaptor_point = affine_from_projective(&adaptor_sum);
    assert!(!bool::from(adaptor_point.is_identity()));
    let adaptor_y_is_even = y_is_even(&adaptor_point);

    let ctx_hash = bridge_context.context_hash();
    let gs_digest = bridge_context.gs_digest(&encoded_x(&adaptor_point), adaptor_y_is_even);

    // Context binding per spec §3 (DEM-Poseidon AD_core requires vk_hash and x_hash)
    let mut vk_bytes = Vec::new();
    vk.serialize_compressed(&mut vk_bytes)
        .expect("serialize vk");
    let vk_hash = sha256(&vk_bytes);

    let mut x_bytes = Vec::new();
    public_input
        .serialize_compressed(&mut x_bytes)
        .expect("serialize x");
    let x_hash = sha256(&x_bytes);

    // Build PVUGC context inputs used later for final layered ctx_hash
    let epoch_nonce = sha256(b"epoch_nonce");
    let tapleaf_hash_bytes = sha256(b"PVUGC/TAPSCRIPT/COMPUTE");

    // Re-encrypt shares with final context bindings now that adaptor sum is fixed
    // 3-of-3 arming checks
    assert_eq!(participants.len(), 3, "expected 3 operators");
    for op in &operator_armings {
        let aff = op.adaptor_commitment;
        assert!(
            !bool::from(AffinePoint::from(aff).is_identity()),
            "T_i must not be identity"
        );
    }
    let summed_commitments = operator_armings
        .iter()
        .fold(ProjectivePoint::IDENTITY, |acc, operator| {
            acc + ProjectivePoint::from(operator.adaptor_commitment)
        });
    let summed_affine = AffinePoint::from(summed_commitments);
    assert!(
        !bool::from(summed_affine.is_identity()),
        "Σ T_i must not be identity"
    );
    assert_eq!(encoded_x(&summed_affine), encoded_x(&adaptor_point));
    assert_eq!(y_is_even(&summed_affine), adaptor_y_is_even);

    let mut armers: Vec<_> = operator_armings
        .iter()
        .map(|operator| ArmerPublicPackage {
            pubkey_x: encoded_x(&operator.participant.affine()),
            adaptor_commitment_x: encoded_x(&operator.adaptor_commitment),
            column_arms: operator.column_arms.clone(),
            encrypted_share: operator.encrypted_share.clone(),
        })
        .collect();
    armers.sort_by(|a, b| a.pubkey_x.cmp(&b.pubkey_x));

    let taproot_tweak = taproot_tweak_scalar(&aggregated_key, None);
    let taproot_output_key = taproot_output_key(&aggregated_key, None);
    let p2tr_script = build_p2tr_script(&taproot_output_key);
    let summed_commitments = operator_armings
        .iter()
        .fold(ProjectivePoint::IDENTITY, |acc, operator| {
            acc + ProjectivePoint::from(operator.adaptor_commitment)
        });
    let summed_affine = affine_from_projective(&summed_commitments);
    assert_eq!(encoded_x(&summed_affine), encoded_x(&adaptor_point));
    assert_eq!(y_is_even(&summed_affine), adaptor_y_is_even);
    let mut deposit_package = DepositPackage {
        ctx_hash,
        gs_digest,
        output_key_x: encoded_x(&taproot_output_key),
        adaptor_point_x: encoded_x(&adaptor_point),
        adaptor_y_is_even,
        musig_l,
        anti_replay: bridge_context.anti_replay.clone(),
        armers,
    };

    let sorted_pk_x: Vec<[u8; 32]> = deposit_package
        .armers
        .iter()
        .map(|armer| armer.pubkey_x)
        .collect();
    let recomputed_l = musig_list_hash_from_pubkeys(&sorted_pk_x);
    assert_eq!(deposit_package.musig_l, recomputed_l);

    // Build Taproot withdrawal template binding to the deposit package hash.
    // In this harness we model the deposit outpoint explicitly so the policy
    // checks can reference a real txid derived from serialized transaction
    // bytes. On mainnet this would be accompanied by an SPV proof that the
    // outpoint pays to the registered script and amount.
    let deposit_value_sat = 150_000u64;
    let deposit_amount = Amount::from_sat(deposit_value_sat);
    let deposit_prevout = TxOut {
        value: deposit_amount,
        script_pubkey: p2tr_script.clone(),
    };
    let deposit_tx = Transaction {
        version: Version::TWO,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint::null(),
            script_sig: ScriptBuf::new(),
            sequence: Sequence::MAX,
            witness: Witness::new(),
        }],
        output: vec![deposit_prevout.clone()],
    };
    let deposit_txid = deposit_tx.txid();
    let deposit_outpoint = OutPoint {
        txid: deposit_txid,
        vout: 0,
    };

    let withdrawal_fee = 5_000u64;
    let withdraw_value_sat =
        deposit_value_sat - withdrawal_fee - bridge_context.anti_replay.cpfp_anchor_value;
    let withdraw_amount = Amount::from_sat(withdraw_value_sat);
    let cpfp_anchor_amount = Amount::from_sat(bridge_context.anti_replay.cpfp_anchor_value);
    let recipient_output_key = Participant::random(&mut rng).affine();
    let recipient_script = build_p2tr_script(&recipient_output_key);
    let cpfp_anchor_script = p2tr_script.clone();

    let (withdraw_tx, prevouts) = assemble_withdrawal_transaction(
        deposit_outpoint,
        deposit_prevout.clone(),
        withdraw_amount,
        recipient_script,
        cpfp_anchor_script,
        cpfp_anchor_amount,
    );
    let withdraw_sighash = taproot_key_spend_sighash(&withdraw_tx, &prevouts);

    // Serialize tx template and rebuild context with txid_template binding
    use bitcoin::consensus::encode::serialize;
    let tx_template_bytes = serialize(&withdraw_tx);
    // Build layered ctx_hash later after pre-signature is available

    // Publish adaptor pre-signature for the frozen withdrawal SIGHASH
    let nonces: Vec<_> = (0..participants.len())
        .map(|_| Nonce::random(&mut rng))
        .collect();
    let (aggregated_nonce, nonce_negated) = aggregate_nonces(&nonces);
    let challenge = bip340_challenge(
        &encoded_x(&aggregated_nonce),
        &deposit_package.output_key_x,
        &withdraw_sighash,
    );
    let mut masked_partials = Vec::with_capacity(participants.len());
    for (((participant, coeff), nonce), operator) in participants
        .iter()
        .zip(coefficients.iter())
        .zip(nonces.iter())
        .zip(operator_armings.iter())
    {
        let nonce_secret = if nonce_negated {
            neg_scalar(&nonce.secret)
        } else {
            nonce.secret
        };
        let mut partial = nonce_secret;
        partial += *coeff * participant.secret * challenge;
        partial -= operator.adaptor_share;
        masked_partials.push(partial);
    }

    let mut presign_s = Scalar::ZERO;
    for masked in &masked_partials {
        presign_s += *masked;
    }
    presign_s += taproot_tweak * challenge;

    let signer_set: Vec<[u8; 32]> = participants
        .iter()
        .map(|p| encoded_x(&p.affine()))
        .collect();
    let pre_signature = PreSignaturePackage {
        aggregated_nonce,
        s_prime: presign_s,
        message: withdraw_sighash,
        nonce_negated,
        signer_set: signer_set.clone(),
        musig_l,
        output_key_x: deposit_package.output_key_x,
        adaptor_point_x: deposit_package.adaptor_point_x,
        adaptor_y_is_even,
    };
    let pre_signature_hash = pre_signature.hash();

    // Build full layered ctx_hash (arming + presig packages)
    use arkworks_groth16::ctx::PvugcContextBuilder;
    // Arming package: concatenate all column_arms bytes as armed_bases; empty header_meta for test
    let mut armed_bases_all = Vec::new();
    for op in &operator_armings {
        op.column_arms
            .serialize_compressed(&mut armed_bases_all)
            .expect("serialize column arms");
    }
    let arming_pkg_hash = PvugcContextBuilder::build_arming_pkg_hash(&armed_bases_all, &[]);
    // Presig package
    let r_bytes = {
        let x = encoded_x(&aggregated_nonce);
        let mut v = Vec::with_capacity(33);
        v.extend_from_slice(&[0x02]);
        v.extend_from_slice(&x);
        v
    };
    let t_bytes = {
        let x = encoded_x(&adaptor_point);
        let mut v = Vec::with_capacity(33);
        v.extend_from_slice(&[0x02]);
        v.extend_from_slice(&x);
        v
    };
    let mut signer_set_bytes = Vec::new();
    for pkx in &signer_set {
        signer_set_bytes.extend_from_slice(pkx);
    }
    let presig_pkg_hash = PvugcContextBuilder::build_presig_pkg_hash(
        &withdraw_sighash,
        &t_bytes,
        &r_bytes,
        &signer_set_bytes,
        &musig_l,
    );
    // Finalize ctx_hash
    let full_ctx = PvugcContextBuilder::new(vk_hash, x_hash, [0u8; 32], epoch_nonce)
        .with_tapleaf(tapleaf_hash_bytes, 0xc0)
        .with_txid_template(tx_template_bytes.clone())
        .with_path_tag("compute")
        .finalize(Some(arming_pkg_hash), Some(presig_pkg_hash));
    let ctx_hash_final = full_ctx.ctx_hash;

    // Encrypt shares now with full-layered AD_core (using ctx_hash)
    for (idx, operator) in operator_armings.iter_mut().enumerate() {
        let share_bytes = scalar_to_bytes(&operator.adaptor_share);
        let t_i = {
            let aff = operator.adaptor_commitment;
            let x = encoded_x(&aff);
            let mut v = Vec::with_capacity(33);
            let tag = if y_is_even(&aff) { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&x);
            v
        };
        let t_agg = {
            let mut v = Vec::with_capacity(33);
            let tag = if adaptor_y_is_even { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&encoded_x(&adaptor_point));
            v
        };
        let mut bases_bytes = Vec::new();
        operator
            .column_arms
            .serialize_compressed(&mut bases_bytes)
            .expect("serialize column arms");
        let ad_core = AdCore::new(
            vk_hash,
            x_hash,
            ctx_hash_final,
            tapleaf_hash_bytes,
            0xc0,
            tx_template_bytes.clone(),
            "compute",
            idx as u32,
            t_i,
            t_agg,
            bases_bytes,
            Vec::new(),
            gs_digest,
        );
        let ad_bytes = ad_core.serialize();
        let ciphertext =
            OneSidedPvugc::encrypt_with_key_dem(&operator.expected_key, &ad_bytes, &share_bytes)
                .expect("encrypt share (DEM-Poseidon)");
        let tau = OneSidedPvugc::compute_key_commitment_tag_dem(
            &operator.expected_key,
            &ad_bytes,
            &ciphertext,
        );
        // Arm-time PoCE-A attestation (ρ-consistency + ciphertext/tag binding)
        // Use pairing-curve (s_i, T_i) for PoCE-A; Bitcoin's secp256k1 PoK is orthogonal
        let s_i_pairing = Fr::rand(&mut rng);
        let t_i_pairing = (<E as Pairing>::G1::generator() * s_i_pairing).into_affine();
        let column_attestation = OneSidedPvugc::attest_column_arming(
            &bases,
            &operator.column_arms,
            &t_i_pairing,
            &rhos[idx],
            &s_i_pairing,
            &operator.expected_key,
            &ad_bytes,
            &ctx_hash_final,
            &gs_digest,
            &ciphertext,
            &tau,
            &mut rng,
        )
        .expect("column attestation");
        assert!(OneSidedPvugc::verify_column_arming(
            &bases,
            &operator.column_arms,
            &t_i_pairing,
            &column_attestation,
            &ad_bytes,
            &ctx_hash_final,
            &gs_digest,
            &ciphertext,
            &tau,
        ));
        // Schnorr PoK on secp256k1 for T_i = s_i·G (bind to context)
        let mut pok_hasher = Sha256::new();
        pok_hasher.update(b"PVUGC/AdaptorPoK");
        pok_hasher.update(&ctx_hash_final);
        pok_hasher.update(&encoded_x(&operator.adaptor_commitment));
        pok_hasher.update(&(idx as u32).to_le_bytes());
        pok_hasher.update(&gs_digest);
        let pok_digest = pok_hasher.finalize();
        let mut pok_msg = [0u8; 32];
        pok_msg.copy_from_slice(&pok_digest);
        let pok_sig = bip340_sign_with_scalar(&operator.adaptor_share, &pok_msg, &mut rng);
        assert!(verify_schnorr_signature(
            &operator.adaptor_commitment,
            &pok_msg,
            &pok_sig
        ));
        operator.encrypted_share = EncryptedShare {
            ciphertext,
            tau: tau.to_vec(),
        };
    }
    // Recompute armers and deposit package with updated encrypted shares
    armers = operator_armings
        .iter()
        .map(|operator| ArmerPublicPackage {
            pubkey_x: encoded_x(&operator.participant.affine()),
            adaptor_commitment_x: encoded_x(&operator.adaptor_commitment),
            column_arms: operator.column_arms.clone(),
            encrypted_share: operator.encrypted_share.clone(),
        })
        .collect();
    deposit_package = DepositPackage {
        ctx_hash: ctx_hash_final,
        gs_digest,
        output_key_x: encoded_x(&taproot_output_key),
        adaptor_point_x: encoded_x(&adaptor_point),
        adaptor_y_is_even,
        musig_l,
        anti_replay: bridge_context.anti_replay.clone(),
        armers,
    };
    let deposit_id = deposit_package.hash();

    // Ready attestation binds the context, package hash and pre-signature hash
    let mut ready_hasher = Sha256::new();
    ready_hasher.update(&ctx_hash_final);
    ready_hasher.update(&deposit_id);
    ready_hasher.update(&pre_signature_hash);
    ready_hasher.update(&bridge_context.anti_replay.to_bytes());
    ready_hasher.update(&deposit_amount.to_sat().to_le_bytes());
    ready_hasher.update(&(p2tr_script.len() as u64).to_le_bytes());
    ready_hasher.update(p2tr_script.as_bytes());
    let ready_digest = ready_hasher.finalize();
    let mut ready_message = [0u8; 32];
    ready_message.copy_from_slice(&ready_digest);

    let attestation = ReadyAttestation::sign(&participants, ready_message, &mut rng);
    assert!(attestation.verify(&participants));

    // === Phase B: deposits must match the registered package ===
    struct DepositEvent {
        outpoint: OutPoint,
        script_pubkey: ScriptBuf,
        value: Amount,
    }

    let deposit_event = DepositEvent {
        outpoint: deposit_outpoint,
        script_pubkey: p2tr_script.clone(),
        value: deposit_amount,
    };

    let policy_accepts = deposit_event.outpoint.txid == deposit_txid
        && deposit_event.script_pubkey == p2tr_script
        && deposit_event.value == deposit_amount;
    assert!(policy_accepts, "registered deposit should be accepted");

    let wrong_txid_hash = sha256(b"wrong-txid");
    let wrong_output_key = Participant::random(&mut rng).affine();
    let wrong_event = DepositEvent {
        outpoint: OutPoint {
            txid: Txid::from_slice(&wrong_txid_hash).unwrap(),
            vout: 0,
        },
        script_pubkey: build_p2tr_script(&wrong_output_key),
        value: deposit_amount,
    };
    let policy_rejects =
        wrong_event.outpoint.txid != deposit_txid || wrong_event.script_pubkey != p2tr_script;
    assert!(policy_rejects, "unregistered deposit must be rejected");

    // === Phase C: proof, decapsulation and spend ===
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    recorder.set_num_instance_variables(vk.gamma_abc_g1.len());
    let proof =
        Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder)
            .unwrap();
    let commitments = commitments_from_recorder(&recorder);
    let bundle = PvugcBundle {
        groth16_proof: proof.clone(),
        dlrep_b: recorder.create_dlrep_b(&pvugc_vk, &vk, &statement_x, &mut rng),
        dlrep_ties: recorder.create_dlrep_ties(&mut rng),
        gs_commitments: commitments.clone(),
    };
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &statement_x));

    let mut recovered_shares = Vec::new();
    for (idx, operator) in operator_armings.iter().enumerate() {
        let derived_key = OneSidedPvugc::decapsulate(&commitments, &operator.column_arms).unwrap();
        assert_eq!(operator.expected_key, derived_key);
        // Rebuild AD_core for this operator
        let t_i = {
            let aff = operator.adaptor_commitment;
            let x = encoded_x(&aff);
            let mut v = Vec::with_capacity(33);
            let tag = if y_is_even(&aff) { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&x);
            v
        };
        let t_agg = {
            let mut v = Vec::with_capacity(33);
            let tag = if adaptor_y_is_even { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&encoded_x(&adaptor_point));
            v
        };
        let mut bases_bytes = Vec::new();
        operator
            .column_arms
            .serialize_compressed(&mut bases_bytes)
            .expect("serialize column arms");
        let ad_core = AdCore::new(
            vk_hash,
            x_hash,
            ctx_hash_final,
            tapleaf_hash_bytes,
            0xc0,
            tx_template_bytes.clone(),
            "compute",
            idx as u32,
            t_i,
            t_agg,
            bases_bytes,
            Vec::new(),
            gs_digest,
        );
        let ad_bytes = ad_core.serialize();
        assert!(OneSidedPvugc::verify_key_commitment_dem(
            &derived_key,
            &ad_bytes,
            &operator.encrypted_share.ciphertext,
            &{
                let mut a = [0u8; 32];
                a.copy_from_slice(&operator.encrypted_share.tau);
                a
            },
        ));
        // Tag round-trip: recompute and compare with published τ
        let tau_re = OneSidedPvugc::compute_key_commitment_tag_dem(
            &derived_key,
            &ad_bytes,
            &operator.encrypted_share.ciphertext,
        );
        assert_eq!(operator.encrypted_share.tau, tau_re.to_vec());
        let decrypted = OneSidedPvugc::decrypt_with_key_dem(
            &derived_key,
            &ad_bytes,
            &operator.encrypted_share.ciphertext,
        )
        .expect("decrypt share");
        assert_eq!(decrypted.len(), 32);
        let mut share_bytes = [0u8; 32];
        share_bytes.copy_from_slice(&decrypted);
        let share_scalar = scalar_from_bytes_strict(&share_bytes);
        assert!(
            !bool::from(share_scalar.is_zero()),
            "adaptor share must be non-zero"
        );
        recovered_shares.push(share_scalar);
    }

    let mut adaptor_secret = Scalar::ZERO;
    for share in &recovered_shares {
        adaptor_secret += *share;
    }

    let adaptor_point_projective = recovered_shares
        .iter()
        .fold(ProjectivePoint::IDENTITY, |acc, share| {
            acc + ProjectivePoint::GENERATOR * share
        });
    let derived_adaptor_point = affine_from_projective(&adaptor_point_projective);
    assert_eq!(
        encoded_x(&derived_adaptor_point),
        deposit_package.adaptor_point_x
    );
    assert_eq!(
        y_is_even(&derived_adaptor_point),
        deposit_package.adaptor_y_is_even
    );

    let pre_sig_bytes = signature_bytes(&pre_signature.aggregated_nonce, &pre_signature.s_prime);
    assert!(!verify_schnorr_signature(
        &taproot_output_key,
        &pre_signature.message,
        &pre_sig_bytes
    ));

    let final_s = pre_signature.s_prime + adaptor_secret;
    let final_sig_bytes = signature_bytes(&pre_signature.aggregated_nonce, &final_s);
    assert!(verify_schnorr_signature(
        &taproot_output_key,
        &pre_signature.message,
        &final_sig_bytes
    ));
    assert!(
        !verify_schnorr_signature(&aggregated_key, &pre_signature.message, &final_sig_bytes),
        "Taproot spends must verify under the tweaked output key, not the internal key"
    );

    let extracted_alpha = final_s - pre_signature.s_prime;
    assert_eq!(
        scalar_to_bytes(&extracted_alpha),
        scalar_to_bytes(&adaptor_secret)
    );

    // Missing share blocks the spend
    let mut incomplete_alpha = Scalar::ZERO;
    for share in recovered_shares.iter().take(2) {
        incomplete_alpha += *share;
    }
    let incomplete_sig = signature_bytes(
        &pre_signature.aggregated_nonce,
        &(pre_signature.s_prime + incomplete_alpha),
    );
    assert!(!verify_schnorr_signature(
        &taproot_output_key,
        &pre_signature.message,
        &incomplete_sig
    ));

    // Tampering with the ciphertext or proof is detected by the key commitment
    let mut tampered_ciphertext = operator_armings[0].encrypted_share.ciphertext.clone();
    tampered_ciphertext[0] ^= 1;
    let derived_key =
        OneSidedPvugc::decapsulate(&commitments, &operator_armings[0].column_arms).unwrap();

    // Rebuild AD_core for operator 0
    let op0 = &operator_armings[0];
    let t_i0 = {
        let aff = op0.adaptor_commitment;
        let x = encoded_x(&aff);
        let mut v = Vec::with_capacity(33);
        let tag = if y_is_even(&aff) { 0x02 } else { 0x03 };
        v.extend_from_slice(&[tag]);
        v.extend_from_slice(&x);
        v
    };
    let t_agg0 = {
        let mut v = Vec::with_capacity(33);
        let tag = if adaptor_y_is_even { 0x02 } else { 0x03 };
        v.extend_from_slice(&[tag]);
        v.extend_from_slice(&encoded_x(&adaptor_point));
        v
    };
    let mut bases_bytes0 = Vec::new();
    op0.column_arms
        .serialize_compressed(&mut bases_bytes0)
        .expect("serialize column arms");
    let ad_core0 = AdCore::new(
        vk_hash,
        x_hash,
        ctx_hash_final,
        tapleaf_hash_bytes,
        0xc0,
        tx_template_bytes.clone(),
        "compute",
        0,
        t_i0.clone(),
        t_agg0.clone(),
        bases_bytes0.clone(),
        Vec::new(),
        gs_digest,
    );
    let ad_bytes0 = ad_core0.serialize();

    assert!(!OneSidedPvugc::verify_key_commitment_dem(
        &derived_key,
        &ad_bytes0,
        &tampered_ciphertext,
        &{
            let mut a = [0u8; 32];
            a.copy_from_slice(&operator_armings[0].encrypted_share.tau);
            a
        },
    ));

    // Context drift (wrong arm attestation bindings) prevents decryption
    let mismatched_ctx = sha256(b"wrong-context");
    let ad_core_mismatch = AdCore::new(
        vk_hash,
        x_hash,
        mismatched_ctx,
        tapleaf_hash_bytes,
        0xc0,
        tx_template_bytes.clone(),
        "compute",
        0,
        t_i0,
        t_agg0,
        bases_bytes0,
        Vec::new(),
        gs_digest,
    );
    let ad_bytes_mismatch = ad_core_mismatch.serialize();
    assert!(!OneSidedPvugc::verify_key_commitment_dem(
        &derived_key,
        &ad_bytes_mismatch,
        &operator_armings[0].encrypted_share.ciphertext,
        &{
            let mut a = [0u8; 32];
            a.copy_from_slice(&operator_armings[0].encrypted_share.tau);
            a
        },
    ));
    // Decryption with mismatched AD_core yields wrong bytes (but still returns Ok)
    let wrong_decrypted = OneSidedPvugc::decrypt_with_key_dem(
        &derived_key,
        &ad_bytes_mismatch,
        &operator_armings[0].encrypted_share.ciphertext,
    )
    .expect("decrypt produced bytes despite mismatch");
    assert_ne!(
        wrong_decrypted,
        scalar_to_bytes(&operator_armings[0].adaptor_share).to_vec(),
        "mismatched context must not yield the original share bytes",
    );

    // Proof for a different statement yields unrelated keys and cannot satisfy
    // the published commitments.
    let wrong_public_input = Fr::from(16u64);
    let wrong_witness = Fr::from(4u64);
    let wrong_circuit = SquareCircuit {
        x: Some(wrong_public_input),
        y: Some(wrong_witness),
    };
    let mut wrong_recorder = SimpleCoeffRecorder::<E>::new();
    wrong_recorder.set_num_instance_variables(vk.gamma_abc_g1.len());
    let _wrong_proof = Groth16::<E>::create_random_proof_with_hook(
        wrong_circuit,
        &pk,
        &mut rng,
        &mut wrong_recorder,
    )
    .unwrap();
    let wrong_commitments = commitments_from_recorder(&wrong_recorder);
    for (idx, operator) in operator_armings.iter().enumerate() {
        let wrong_key =
            OneSidedPvugc::decapsulate(&wrong_commitments, &operator.column_arms).unwrap();
        assert_ne!(wrong_key, operator.expected_key);
        // Rebuild AD_core exactly as in the honest path for this operator
        let t_i = {
            let aff = operator.adaptor_commitment;
            let x = encoded_x(&aff);
            let mut v = Vec::with_capacity(33);
            let tag = if y_is_even(&aff) { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&x);
            v
        };
        let t_agg = {
            let mut v = Vec::with_capacity(33);
            let tag = if adaptor_y_is_even { 0x02 } else { 0x03 };
            v.extend_from_slice(&[tag]);
            v.extend_from_slice(&encoded_x(&adaptor_point));
            v
        };
        let mut bases_bytes = Vec::new();
        operator
            .column_arms
            .serialize_compressed(&mut bases_bytes)
            .expect("serialize column arms");
        let ad_core = AdCore::new(
            vk_hash,
            x_hash,
            ctx_hash_final,
            tapleaf_hash_bytes,
            0xc0,
            tx_template_bytes.clone(),
            "compute",
            idx as u32,
            t_i,
            t_agg,
            bases_bytes,
            Vec::new(),
            gs_digest,
        );
        let ad_bytes = ad_core.serialize();
        assert!(!OneSidedPvugc::verify_key_commitment_dem(
            &wrong_key,
            &ad_bytes,
            &operator.encrypted_share.ciphertext,
            &{
                let mut a = [0u8; 32];
                a.copy_from_slice(&operator.encrypted_share.tau);
                a
            },
        ));
    }
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    let digest = Sha256::digest(bytes);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn commitments_from_recorder<Ep: Pairing>(
    recorder: &SimpleCoeffRecorder<Ep>,
) -> OneSidedCommitments<Ep> {
    recorder.build_commitments()
}

fn bip340_single_sign(participant: &Participant, msg: &[u8], rng: &mut StdRng) -> [u8; 64] {
    let nonce = Nonce::random(rng);
    let mut r_affine = AffinePoint::from(nonce.public);
    let mut nonce_secret = nonce.secret;
    if !y_is_even(&r_affine) {
        r_affine = AffinePoint::from(-nonce.public);
        nonce_secret = -nonce_secret;
    }
    let pk_affine = participant.affine();
    let e = bip340_challenge(&encoded_x(&r_affine), &encoded_x(&pk_affine), msg);
    let s = nonce_secret + participant.secret * e;
    signature_bytes(&r_affine, &s)
}

fn bip340_sign_with_scalar(secret: &Scalar, msg: &[u8; 32], rng: &mut StdRng) -> [u8; 64] {
    let nonce = Nonce::random(rng);
    let mut r_affine = AffinePoint::from(nonce.public);
    let mut k = nonce.secret;
    if !y_is_even(&r_affine) {
        r_affine = AffinePoint::from(-nonce.public);
        k = -k;
    }
    let pk_affine = AffinePoint::from(ProjectivePoint::GENERATOR * *secret);
    let e = bip340_challenge(&encoded_x(&r_affine), &encoded_x(&pk_affine), msg);
    let s = k + (*secret) * e;
    signature_bytes(&r_affine, &s)
}

#[test]
fn test_pvugc_bitcoin_adaptor_armtime_rejects_invalid_pok_or_poce() {
    let mut rng = StdRng::seed_from_u64(4242);

    // Proving system setup
    let public_input = Fr::from(25u64);
    let witness = Fr::from(5u64);
    let circuit = SquareCircuit {
        x: Some(public_input),
        y: Some(witness),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Shared column bases for PoCE-A
    let statement_x = vec![public_input];
    let bases = OneSidedPvugc::build_column_bases(&pvugc_vk, &vk, &statement_x)
        .expect("build_column_bases");

    // Participants
    let mut participants = vec![
        Participant::random(&mut rng),
        Participant::random(&mut rng),
        Participant::random(&mut rng),
    ];
    participants.sort_by(|a, b| encoded_x(&a.affine()).cmp(&encoded_x(&b.affine())));

    // Arming
    let mut operator_armings = Vec::new();
    let mut expected_keys = Vec::new();
    let mut rhos: Vec<Fr> = Vec::new();
    for _ in &participants {
        let share = loop {
            let candidate = Scalar::random(&mut rng);
            if bool::from(candidate.is_zero()) {
                continue;
            }
            break candidate;
        };
        let commitment = AffinePoint::from(ProjectivePoint::GENERATOR * share);
        let rho = Fr::rand(&mut rng);
        rhos.push(rho);
        let (_bases, col_arms, _r, k) =
            OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &statement_x, &rho).unwrap();
        operator_armings.push((share, commitment, col_arms));
        expected_keys.push(k);
    }

    // Minimal bindings for challenge inputs
    let ctx_hash = [0u8; 32];
    let gs_digest = [1u8; 32];
    let ad_core = AdCore::new(
        [0u8; 32],
        [0u8; 32],
        ctx_hash,
        [9u8; 32],
        0xc0,
        Vec::new(),
        "compute",
        0,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        gs_digest,
    );
    let ad_bytes = ad_core.serialize();

    // Evaluate PoK and PoCE-A for all operators; gate pre-sign on all passing
    let mut pok_ok = vec![false; participants.len()];
    let mut poce_ok = vec![false; participants.len()];
    for (i, (share, commitment, col_arms)) in operator_armings.iter().enumerate() {
        // Build context-bound PoK message
        let mut pok_hasher = Sha256::new();
        pok_hasher.update(b"PVUGC/AdaptorPoK");
        pok_hasher.update(&ctx_hash);
        pok_hasher.update(&encoded_x(commitment));
        pok_hasher.update(&(i as u32).to_le_bytes());
        pok_hasher.update(&gs_digest);
        let digest = pok_hasher.finalize();
        let mut msg = [0u8; 32];
        msg.copy_from_slice(&digest);

        // PoK: operator 1 uses wrong secret to simulate failure
        let secret = if i == 1 { *share + Scalar::ONE } else { *share };
        let sig = bip340_sign_with_scalar(&secret, &msg, &mut rng);
        pok_ok[i] = verify_schnorr_signature(commitment, &msg, &sig);

        // PoCE-A: operator 2 uses wrong rho to simulate failure
        let s_i_pairing = Fr::rand(&mut rng);
        let t_i_pairing = (<E as Pairing>::G1::generator() * s_i_pairing).into_affine();
        let rho_use = if i == 2 {
            rhos[i] + Fr::from(1u64)
        } else {
            rhos[i]
        };
        let key = &expected_keys[i];
        let key_bytes = serialize_gt::<E>(&key.0);
        let plaintext = scalar_to_bytes(share);
        let dem = DemP2::new(&key_bytes, &ad_bytes);
        let ciphertext = dem.encrypt(&plaintext);
        let tau = OneSidedPvugc::compute_key_commitment_tag_dem(key, &ad_bytes, &ciphertext);
        let column_attestation = OneSidedPvugc::attest_column_arming(
            &bases,
            col_arms,
            &t_i_pairing,
            &rho_use,
            &s_i_pairing,
            key,
            &ad_bytes,
            &ctx_hash,
            &gs_digest,
            &ciphertext,
            &tau,
            &mut rng,
        )
        .expect("column attestation");
        poce_ok[i] = OneSidedPvugc::verify_column_arming(
            &bases,
            col_arms,
            &t_i_pairing,
            &column_attestation,
            &ad_bytes,
            &ctx_hash,
            &gs_digest,
            &ciphertext,
            &tau,
        );
    }

    let pre_sign_allowed = pok_ok.iter().all(|&b| b) && poce_ok.iter().all(|&b| b);
    assert!(
        !pre_sign_allowed,
        "pre-sign MUST NOT proceed when any PoK or PoCE-A fails"
    );
}

#[test]
fn test_pvugc_bitcoin_adaptor_late_fail_without_gating() {
    // This test intentionally skips arm-time gating to demonstrate late cryptographic failure
    // (PoCE-B rejection) when an operator publishes mismatched arms vs ciphertext key.
    let mut rng = StdRng::seed_from_u64(7777);

    // Proving system setup
    let public_input = Fr::from(25u64);
    let witness = Fr::from(5u64);
    let circuit = SquareCircuit {
        x: Some(public_input),
        y: Some(witness),
    };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    // Build bases and a valid commitments bundle for the statement
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    recorder.set_num_instance_variables(vk.gamma_abc_g1.len());
    let _proof =
        Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder)
            .unwrap();
    let commitments = commitments_from_recorder(&recorder);
    let statement_x = vec![public_input];
    let bases = OneSidedPvugc::build_column_bases(&pvugc_vk, &vk, &statement_x).expect("bases");
    assert_eq!(commitments.x_b_cols.len(), bases.y_cols.len());

    // Construct a malicious operator with mismatched (arms rho) vs (encryption key rho)
    let rho_right = Fr::rand(&mut rng);
    let rho_wrong = rho_right + Fr::from(1u64);
    // Use API to get R and the correct key K_right = R^{rho_right}
    let (_bases_tmp, _col_arms_right, _r_target, k_right) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &statement_x, &rho_right).unwrap();
    // Publish wrong arms using rho_wrong
    let col_arms_wrong =
        arkworks_groth16::arming::arm_columns(&bases, &rho_wrong).expect("arm_columns");

    // Build minimal AD_core and encrypt under K_right
    let vk_hash = [0u8; 32];
    let x_hash = [0u8; 32];
    let ctx_hash = [0u8; 32];
    let gs_digest = [1u8; 32];
    let ad_core = AdCore::new(
        vk_hash,
        x_hash,
        ctx_hash,
        [9u8; 32],
        0xc0,
        Vec::new(),
        "compute",
        0,
        vec![0u8; 33],
        vec![0u8; 33],
        Vec::new(),
        Vec::new(),
        gs_digest,
    );
    let ad_bytes = ad_core.serialize();
    let share_bytes = [7u8; 32];
    let ciphertext =
        OneSidedPvugc::encrypt_with_key_dem(&k_right, &ad_bytes, &share_bytes).expect("encrypt");
    let tau = OneSidedPvugc::compute_key_commitment_tag_dem(&k_right, &ad_bytes, &ciphertext);

    // At decap-time, the derived key from wrong arms is K_wrong = R^{rho_wrong}
    let k_wrong = OneSidedPvugc::decapsulate(&commitments, &col_arms_wrong).expect("decap");
    // PoCE-B key-commit must reject because ciphertext/tag were made with K_right, not K_wrong
    assert!(!OneSidedPvugc::verify_key_commitment_dem(
        &k_wrong,
        &ad_bytes,
        &ciphertext,
        &{
            let mut a = [0u8; 32];
            a.copy_from_slice(&tau);
            a
        }
    ));

    // Decryption with K_wrong yields wrong bytes (but still returns Ok), adapter cannot be completed
    let wrong_plain =
        OneSidedPvugc::decrypt_with_key_dem(&k_wrong, &ad_bytes, &ciphertext).expect("decrypt");
    assert_ne!(
        wrong_plain, share_bytes,
        "mismatched arms must not yield the original share"
    );
}
