//! Offline cancellation of a synthetic UTXO using the reduced Praxis profile.

use bitcoin::absolute::LockTime;
use bitcoin::hashes::Hash;
use bitcoin::secp256k1::{schnorr, Message, Secp256k1, XOnlyPublicKey};
use bitcoin::sighash::TapSighashType;
use bitcoin::{
    transaction, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid, Witness,
};
use k256::elliptic_curve::sec1::ToEncodedPoint;
use k256::elliptic_curve::Field;
use k256::{ProjectivePoint, PublicKey, Scalar};
use musig2::secp::{MaybeScalar, Point, Scalar as SigningScalar};
use musig2::{
    adaptor, AdaptorSignature, AggNonce, BinaryEncoding, KeyAggContext, PartialSignature, SecNonce,
};
use pvugc_praxis::bitcoin_adapter::{build_p2tr_script, taproot_key_spend_sighash};
use pvugc_praxis::ceremony::wire::{archive_id, encode_public, recover_public};
use pvugc_praxis::ceremony::{arm, create_coin, Frozen, Slot};
use rand::{CryptoRng, Rng, RngCore};

use sha2::{Digest, Sha256};
use std::error::Error;
use std::io::Read;

pub type DemoResult<T> = Result<T, Box<dyn Error>>;
const SIGNERS: usize = 3;
pub const RECEIPT_LEN: usize = 8 + 32 + 32 + 4 + 2 + 33 + 65 + SIGNERS * 33;

pub struct Receipt {
    pub archive_hash: [u8; 32],
    pub archive_len: usize,
    pub rounds: usize,
    pub slot: Slot,
    pub roster: Vec<(u32, ProjectivePoint)>,
    pub output_key: Point,
    pub presignature: AdaptorSignature,
}

pub fn receipt_hash(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

impl Receipt {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(RECEIPT_LEN);
        bytes.extend_from_slice(b"PXBTC001");
        bytes.extend_from_slice(&self.slot.cancel_sighash);
        bytes.extend_from_slice(&self.archive_hash);
        bytes.extend_from_slice(&(self.archive_len as u32).to_be_bytes());
        bytes.extend_from_slice(&(self.rounds as u16).to_be_bytes());
        bytes.extend_from_slice(&self.output_key.serialize());
        bytes.extend_from_slice(&self.presignature.to_bytes());
        for (_, point) in &self.roster {
            bytes.extend_from_slice(point.to_affine().to_encoded_point(true).as_bytes());
        }
        bytes
    }

    pub fn parse(bytes: &[u8], expected_hash: [u8; 32]) -> DemoResult<Self> {
        if bytes.len() != RECEIPT_LEN || receipt_hash(bytes) != expected_hash {
            return Err(
                "setup receipt length or SHA-256 digest differs from the pinned receipt".into(),
            );
        }
        let mut input = bytes;
        fn read<const N: usize>(input: &mut &[u8]) -> DemoResult<[u8; N]> {
            let mut result = [0u8; N];
            input.read_exact(&mut result)?;
            Ok(result)
        }
        if read::<8>(&mut input)? != *b"PXBTC001" {
            return Err("unsupported example receipt format".into());
        }
        let slot = Slot::fixture(read(&mut input)?);
        let archive_hash = read(&mut input)?;
        let archive_len = u32::from_be_bytes(read(&mut input)?) as usize;
        let rounds = u16::from_be_bytes(read(&mut input)?) as usize;
        if !(2..=256).contains(&rounds) || archive_len == 0 || archive_len > 64 * 1024 * 1024 {
            return Err("archive length outside the three-signer demonstration profile".into());
        }
        let output_key = Point::from_slice(&read::<33>(&mut input)?)?;
        let presignature = AdaptorSignature::from_bytes(&read::<65>(&mut input)?)?;
        let mut roster = Vec::with_capacity(SIGNERS);
        for id in 0..SIGNERS {
            let key = PublicKey::from_sec1_bytes(&read::<33>(&mut input)?)?;
            roster.push((id as u32, ProjectivePoint::from(*key.as_affine())));
        }
        let receipt = Self {
            slot,
            archive_hash,
            archive_len,
            rounds,
            output_key,
            presignature,
            roster,
        };
        let (cancel, prevout) = cancellation(output_key);
        if taproot_key_spend_sighash(&cancel, &[prevout]) != slot.cancel_sighash {
            return Err("receipt does not identify the fixed synthetic cancellation".into());
        }
        let adaptor_point = aggregate_point(receipt.roster.iter().map(|(_, p)| *p))?;
        adaptor::verify_single(
            output_key,
            &receipt.presignature,
            slot.cancel_sighash,
            adaptor_point,
        )?;
        Ok(receipt)
    }

    pub fn shares(&self, archive: &[u8], witness: [bool; 2]) -> DemoResult<Vec<Scalar>> {
        Ok(recover_public(
            archive,
            self.slot,
            &self.roster,
            self.rounds,
            witness,
            self.archive_hash,
        )?)
    }

    pub fn signature(&self, shares: &[Scalar]) -> DemoResult<bitcoin::taproot::Signature> {
        let sum = shares.iter().fold(Scalar::ZERO, |acc, &share| acc + share);
        let sig: [u8; 64] = self
            .presignature
            .adapt(MaybeScalar::from_slice(&sum.to_bytes())?)
            .ok_or("invalid adapted signature")?;
        let sig = bitcoin::taproot::Signature {
            sig: schnorr::Signature::from_slice(&sig)?,
            hash_ty: TapSighashType::All,
        };
        let (cancel, prevout) = cancellation(self.output_key);
        verify(&cancel, &prevout, &sig)?;
        Ok(sig)
    }
}

pub fn verify(
    cancel: &Transaction,
    prevout: &TxOut,
    signature: &bitcoin::taproot::Signature,
) -> DemoResult<()> {
    if signature.hash_ty != TapSighashType::All || !prevout.script_pubkey.is_p2tr() {
        return Err("unexpected script or sighash type".into());
    }
    let message = Message::from_digest_slice(&taproot_key_spend_sighash(
        cancel,
        std::slice::from_ref(prevout),
    ))?;
    let output_x = XOnlyPublicKey::from_slice(&prevout.script_pubkey.as_bytes()[2..])?;
    Ok(Secp256k1::verification_only().verify_schnorr(&signature.sig, &message, &output_x)?)
}

fn aggregate_point(points: impl Iterator<Item = ProjectivePoint>) -> DemoResult<Point> {
    let aggregate = points.fold(ProjectivePoint::IDENTITY, |acc, p| acc + p);
    Ok(Point::from_slice(
        aggregate.to_affine().to_encoded_point(true).as_bytes(),
    )?)
}

fn sign_cancel<R: RngCore + CryptoRng>(
    signers: Vec<SigningScalar>,
    keys: &KeyAggContext,
    message: [u8; 32],
    adaptor_point: Point,
    rng: &mut R,
) -> DemoResult<AdaptorSignature> {
    let output_key: Point = keys.aggregated_pubkey();
    let nonces: Vec<_> = signers
        .iter()
        .map(|&key| {
            SecNonce::build(rng.gen::<[u8; 32]>())
                .with_seckey(key)
                .with_message(&message)
                .with_aggregated_pubkey(output_key)
                .with_extra_input(&adaptor_point.serialize())
                .build()
        })
        .collect();
    let public_nonces: Vec<_> = nonces.iter().map(SecNonce::public_nonce).collect();
    let aggregate_nonce = AggNonce::sum(&public_nonces);
    let mut partials = Vec::<PartialSignature>::new();
    for ((key, nonce), public_nonce) in signers.into_iter().zip(nonces).zip(&public_nonces) {
        let partial =
            adaptor::sign_partial(keys, key, nonce, &aggregate_nonce, adaptor_point, message)?;
        adaptor::verify_partial(
            keys,
            partial,
            &aggregate_nonce,
            adaptor_point,
            key.base_point_mul(),
            public_nonce,
            message,
        )?;
        partials.push(partial);
    }
    let signature = adaptor::aggregate_partial_signatures(
        keys,
        &aggregate_nonce,
        adaptor_point,
        partials,
        message,
    )?;
    adaptor::verify_single(output_key, &signature, message, adaptor_point)?;
    Ok(signature)
}

pub fn cancellation(output_key: Point) -> (Transaction, TxOut) {
    let output_pubkey = PublicKey::from_sec1_bytes(&output_key.serialize()).unwrap();
    let prevout = TxOut {
        value: Amount::from_sat(100_000),
        script_pubkey: build_p2tr_script(output_pubkey.as_affine()),
    };
    let cancel = Transaction {
        version: transaction::Version::TWO,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint::new(Txid::from_byte_array([0x42; 32]), 1),
            script_sig: ScriptBuf::new(),
            sequence: Sequence::MAX,
            witness: Witness::new(),
        }],
        output: vec![TxOut {
            value: Amount::from_sat(99_000),
            script_pubkey: prevout.script_pubkey.clone(),
        }],
    };
    (cancel, prevout)
}
pub fn setup<R: RngCore + CryptoRng>(rng: &mut R, rounds: usize) -> DemoResult<(Receipt, Vec<u8>)> {
    let signer_keys: Vec<_> = (0..3)
        .map(|_| SigningScalar::from_slice(&Scalar::random(&mut *rng).to_bytes()))
        .collect::<Result<Vec<_>, _>>()?;
    let keys = KeyAggContext::new(signer_keys.iter().map(|key| key.base_point_mul()))?
        .with_unspendable_taproot_tweak()?;
    let output_key: Point = keys.aggregated_pubkey();
    let (cancel, prevout) = cancellation(output_key);
    let prevouts = [prevout];
    let sighash = taproot_key_spend_sighash(&cancel, &prevouts);
    let slot = Slot::fixture(sighash);
    // Only the public commitments and setup openings survive the ceremony.
    let shares: Vec<_> = (0..SIGNERS as u32)
        .map(|id| (id, Scalar::random(&mut *rng)))
        .collect();
    // The fixture models each signer sending its point through the setup's
    // authenticated roster channel before the capsule packages are assembled.
    let roster: Vec<_> = shares
        .iter()
        .map(|&(id, share)| (id, ProjectivePoint::GENERATOR * share))
        .collect();
    let (packages, private_states): (Vec<_>, Vec<_>) = shares
        .into_iter()
        .map(|(id, share)| arm(&slot, id, share, rounds, rng))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .unzip();
    let frozen = Frozen::new(slot, &roster, packages, rounds)?;
    let adaptor_point = aggregate_point(frozen.adaptor_points())?;
    let (commits, coins): (Vec<_>, Vec<_>) = (0..SIGNERS as u32)
        .map(|i| create_coin(&frozen, i as usize, rng))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .unzip();
    let board = frozen.lock_commits(&commits)?;
    let (seeds, receipts): (Vec<_>, Vec<_>) = coins
        .into_iter()
        .map(|coin| coin.reveal(&board))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .unzip();
    let challenge = board.challenge(&seeds)?;
    let openings = private_states
        .into_iter()
        .enumerate()
        .map(|(i, state)| state.respond(&frozen, &challenge, i, &receipts[i]))
        .collect::<Result<Vec<_>, _>>()?;
    frozen.verify(&challenge, &openings)?;
    let archive = encode_public(&frozen, &commits, &seeds, &openings)?;
    // Save the agreed public digest with the pre-signature at setup.
    let expected_archive = archive_id(&archive);
    let presignature = sign_cancel(signer_keys, &keys, sighash, adaptor_point, rng)?;

    Ok((
        Receipt {
            archive_hash: expected_archive,
            archive_len: archive.len(),
            rounds,
            slot,
            roster,
            output_key,
            presignature,
        },
        archive,
    ))
}
