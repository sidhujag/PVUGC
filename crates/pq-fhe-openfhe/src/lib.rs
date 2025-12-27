use anyhow::{anyhow, Context, Result};
use openfhe::ffi as openfhe_ffi;
use pq_fhe_backend::FheBackend;

use openfhe::cxx::{self, let_cxx_string, CxxVector};
use pq_basis_blob::{rotations_powers_of_two, OpenFheLimbFilesV0, OpenFheManifestV0, ShapeBlobManifestV0, WeightsKind};
use rand_core::{OsRng, RngCore};
use rayon::prelude::*;
use std::sync::Arc;
use std::fs;
use std::path::PathBuf;

pub struct OpenFheBackend;

pub struct OpenFheCtx {
    pub cc: cxx::UniquePtr<openfhe_ffi::CryptoContextDCRTPoly>,
}

pub struct OpenFhePk {
    pub pk: cxx::UniquePtr<openfhe_ffi::PublicKeyDCRTPoly>,
}

pub struct OpenFheSk {
    pub sk: cxx::UniquePtr<openfhe_ffi::PrivateKeyDCRTPoly>,
}

pub struct OpenFheCt {
    pub ct: cxx::UniquePtr<openfhe_ffi::CiphertextDCRTPoly>,
}

pub struct OpenFhePt {
    pub pt: cxx::UniquePtr<openfhe_ffi::Plaintext>,
}

pub struct CtChunkReader {
    r: cxx::UniquePtr<openfhe_ffi::CiphertextStreamReaderDCRTPoly>,
}

fn ct_stream_buffer_bytes_from_env() -> usize {
    // Opt-in: use iostream default buffer unless explicitly set.
    // Value is MiB (so it's convenient to tune on servers).
    let mib = std::env::var("PVUGC_OPENFHE_CT_STREAM_BUF_MIB")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .unwrap_or(0);
    mib.saturating_mul(1024 * 1024)
}

impl CtChunkReader {
    pub fn open(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<Self> {
        let_cxx_string!(p = path);
        let buf = ct_stream_buffer_bytes_from_env();
        let r = if buf == 0 {
            openfhe_ffi::DCRTPolyNewCiphertextStreamReader(&p, serial_mode)
        } else {
            openfhe_ffi::DCRTPolyNewCiphertextStreamReaderWithBuffer(&p, serial_mode, buf)
        };
        if r.is_null() {
            return Err(anyhow!("failed to open ciphertext stream reader: {path}"));
        }
        Ok(Self { r })
    }

    pub fn next(&mut self) -> Result<Option<OpenFheCt>> {
        let ct = self.r.pin_mut().Next();
        if ct.is_null() {
            return Ok(None);
        }
        Ok(Some(OpenFheCt { ct }))
    }
}

pub struct CtChunkWriter {
    w: cxx::UniquePtr<openfhe_ffi::CiphertextStreamWriterDCRTPoly>,
}

impl CtChunkWriter {
    pub fn create(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<Self> {
        let_cxx_string!(p = path);
        let buf = ct_stream_buffer_bytes_from_env();
        let w = if buf == 0 {
            openfhe_ffi::DCRTPolyNewCiphertextStreamWriter(&p, serial_mode, true)
        } else {
            openfhe_ffi::DCRTPolyNewCiphertextStreamWriterWithBuffer(&p, serial_mode, true, buf)
        };
        if w.is_null() {
            return Err(anyhow!("failed to create ciphertext stream writer: {path}"));
        }
        Ok(Self { w })
    }

    pub fn append(&mut self, ct: &cxx::UniquePtr<openfhe_ffi::CiphertextDCRTPoly>) -> Result<()> {
        if !self.w.pin_mut().Append(ct) {
            return Err(anyhow!("append ciphertext failed"));
        }
        Ok(())
    }
}

impl OpenFheBackend {
    pub fn parse_serial_mode(s: &str) -> Result<openfhe_ffi::SerialMode> {
        match s.trim().to_ascii_uppercase().as_str() {
            "BINARY" => Ok(openfhe_ffi::SerialMode::BINARY),
            "JSON" => Ok(openfhe_ffi::SerialMode::JSON),
            _ => Err(anyhow!("invalid serial mode (expected BINARY or JSON)")),
        }
    }

    pub fn deserialize_crypto_context(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<OpenFheCtx> {
        let mut cc = openfhe_ffi::DCRTPolyGenNullCryptoContext();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeCryptoContextFromFile(&p, cc.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize crypto context failed: {path}"));
        }
        Ok(OpenFheCtx { cc })
    }

    pub fn deserialize_public_key(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<OpenFhePk> {
        let mut pk = openfhe_ffi::DCRTPolyGenNullPublicKey();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializePublicKeyFromFile(&p, pk.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize public key failed: {path}"));
        }
        Ok(OpenFhePk { pk })
    }

    pub fn deserialize_private_key(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<OpenFheSk> {
        let mut sk = openfhe_ffi::DCRTPolyGenNullPrivateKey();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializePrivateKeyFromFile(&p, sk.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize private key failed: {path}"));
        }
        Ok(OpenFheSk { sk })
    }

    pub fn deserialize_eval_mult_key(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<()> {
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeEvalMultKeyFromFile(&p, serial_mode) {
            return Err(anyhow!("deserialize eval mult key failed: {path}"));
        }
        Ok(())
    }

    pub fn deserialize_eval_rot_key(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<()> {
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeEvalAutomorphismKeyFromFile(&p, serial_mode) {
            return Err(anyhow!("deserialize eval rot key failed: {path}"));
        }
        Ok(())
    }

    pub fn deserialize_ciphertext(path: &str, serial_mode: openfhe_ffi::SerialMode) -> Result<OpenFheCt> {
        let mut ct = openfhe_ffi::DCRTPolyGenNullCiphertext();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeCiphertextFromFile(&p, ct.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize ciphertext failed: {path}"));
        }
        Ok(OpenFheCt { ct })
    }

    pub fn serialize_ciphertext_to_file(
        path: &str,
        ct: &OpenFheCt,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<()> {
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolySerializeCiphertextToFile(&p, &ct.ct, serial_mode) {
            return Err(anyhow!("serialize ciphertext failed: {path}"));
        }
        Ok(())
    }
}

impl FheBackend for OpenFheBackend {
    type Context = OpenFheCtx;
    type PublicKey = OpenFhePk;
    type PrivateKey = OpenFheSk;
    type Ciphertext = OpenFheCt;
    type Plaintext = OpenFhePt;

    fn make_packed_plaintext(ctx: &Self::Context, values: &[i64]) -> Result<Self::Plaintext> {
        let mut v = CxxVector::<i64>::new();
        for &x in values {
            v.pin_mut().push(x);
        }
        let pt = ctx.cc.MakePackedPlaintext(&v, 1, 0);
        Ok(OpenFhePt { pt })
    }

    fn encrypt(ctx: &Self::Context, pk: &Self::PublicKey, pt: &Self::Plaintext) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EncryptByPublicKey(&pk.pk, &pt.pt),
        })
    }

    fn eval_mult_plain(ctx: &Self::Context, ct: &Self::Ciphertext, pt: &Self::Plaintext) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalMultByCiphertextAndPlaintext(&ct.ct, &pt.pt),
        })
    }

    fn eval_add(ctx: &Self::Context, a: &Self::Ciphertext, b: &Self::Ciphertext) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalAddByCiphertexts(&a.ct, &b.ct),
        })
    }

    fn eval_add_plain(ctx: &Self::Context, a: &Self::Ciphertext, pt: &Self::Plaintext) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalAddByCiphertextAndPlaintext(&a.ct, &pt.pt),
        })
    }

    fn eval_rotate(ctx: &Self::Context, ct: &Self::Ciphertext, shift: i32) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalRotate(&ct.ct, shift),
        })
    }

    fn decrypt(ctx: &Self::Context, sk: &Self::PrivateKey, ct: &Self::Ciphertext) -> Result<Vec<i64>> {
        let mut pt_out = openfhe_ffi::GenNullPlainText();
        ctx.cc
            .DecryptByPrivateKeyAndCiphertext(&sk.sk, &ct.ct, pt_out.pin_mut());
        let packed = pt_out.GetPackedValue();
        let mut out = Vec::with_capacity(packed.len());
        for i in 0..packed.len() {
            out.push(*packed.get(i).unwrap_or(&0));
        }
        Ok(out)
    }
}

/// Dev helper: decrypt and force the plaintext packed length (needed before GetPackedValue()).
pub fn decrypt_packed_with_len(ctx: &OpenFheCtx, sk: &OpenFheSk, ct: &OpenFheCt, len: usize) -> Result<Vec<i64>> {
    let mut pt_out = openfhe_ffi::GenNullPlainText();
    ctx.cc
        .DecryptByPrivateKeyAndCiphertext(&sk.sk, &ct.ct, pt_out.pin_mut());
    pt_out.SetLength(len);
    let packed = pt_out.GetPackedValue();
    let mut out = Vec::with_capacity(packed.len());
    for i in 0..packed.len() {
        out.push(*packed.get(i).unwrap_or(&0));
    }
    Ok(out)
}

/// GPT-Pro blob setup (v0 demo): per-shape OpenFHE key material + basis ciphertexts.
///
/// This is the "shape-CRS" artifact generator. In v0 we also serialize the private key for the
/// fake gate (decrypt+compare). Do NOT ship that in production.
pub struct SetupShapeBlobArgs {
    pub out_dir: PathBuf,
    pub shape_id: String,
    pub n_armers: usize,
    pub s_basis: usize,
    pub d_limbs: usize,
    pub moduli: Vec<u64>,
    pub epoch: u64,
    pub slot_count: usize,
    pub block_count: usize,
    pub blocks_per_chunk: usize,
    pub weights_kind: WeightsKind,
    pub multiplicative_depth: u32,
    pub serial_mode: String,
    /// Parallelism for basis ciphertext generation across `j`.
    ///
    /// IMPORTANT: Some OpenFHE builds appear not to be fully thread-safe for (de)serialization +
    /// encryption in parallel. Default is 1 (safe). Increase cautiously (e.g. 8/16) on servers.
    pub basis_parallelism: usize,
}

pub fn setup_shape_blob_openfhe(args: SetupShapeBlobArgs) -> Result<()> {
    anyhow::ensure!(args.blocks_per_chunk > 0, "blocks_per_chunk must be > 0");
    anyhow::ensure!(args.moduli.len() == args.d_limbs, "moduli.len must equal d_limbs");
    anyhow::ensure!(args.basis_parallelism > 0, "basis_parallelism must be > 0");
    let serial_mode_enum = OpenFheBackend::parse_serial_mode(&args.serial_mode)?;

    fs::create_dir_all(&args.out_dir)?;
    fs::create_dir_all(args.out_dir.join("basis")).ok();
    fs::create_dir_all(args.out_dir.join("openfhe")).ok();

    let mut limb_files: Vec<OpenFheLimbFilesV0> = Vec::with_capacity(args.d_limbs);

    for (limb, &pt_mod) in args.moduli.iter().enumerate() {
        let limb_dir = args.out_dir.join(format!("openfhe/l{limb}"));
        fs::create_dir_all(&limb_dir).ok();

        let mut cc_params = openfhe_ffi::GenParamsBFVRNS();
        cc_params.pin_mut().SetPlaintextModulus(pt_mod);
        cc_params.pin_mut().SetMultiplicativeDepth(args.multiplicative_depth);
        // Ensure packing + modulus sizing are compatible with our chosen plaintext modulus.
        // Without this, OpenFHE can pick CRT moduli smaller than `pt_mod`, causing Encode() to fail.
        cc_params.pin_mut().SetBatchSize(args.slot_count as u32);
        // OpenFHE security checks may require a minimum ring dimension (e.g. 8192 for 128-bit).
        // We only need batch_size = slot_count; ring_dim can be larger.
        let ring_dim = (args.slot_count as u32).next_power_of_two().max(8192);
        cc_params.pin_mut().SetRingDim(ring_dim);
        // Ensure BFVRNS picks CRT moduli comfortably above the plaintext modulus.
        // (BFVRNS in some OpenFHE builds does not support SetFirstModSize().)
        cc_params.pin_mut().SetScalingModSize(60);
        cc_params
            .pin_mut()
            .SetSecurityLevel(openfhe_ffi::SecurityLevel::HEStd_128_classic);

        let cc = openfhe_ffi::DCRTPolyGenCryptoContextByParamsBFVRNS(&cc_params);
        cc.EnableByFeature(openfhe_ffi::PKESchemeFeature::PKE);
        cc.EnableByFeature(openfhe_ffi::PKESchemeFeature::KEYSWITCH);
        cc.EnableByFeature(openfhe_ffi::PKESchemeFeature::LEVELEDSHE);

        let kp = cc.KeyGen();
        cc.EvalMultKeyGen(&kp.GetPrivateKey());

        // Rotation keys: powers of two for SlotSum.
        let mut index_list = CxxVector::<i32>::new();
        for r in rotations_powers_of_two(args.slot_count) {
            index_list.pin_mut().push(r);
        }
        cc.EvalRotateKeyGen(&kp.GetPrivateKey(), &index_list, &openfhe_ffi::DCRTPolyGenNullPublicKey());

        let cc_path = limb_dir.join("crypto_context.bin");
        let pk_path = limb_dir.join("public_key.bin");
        let sk_path = limb_dir.join("private_key.bin");
        let em_path = limb_dir.join("eval_mult_key.bin");
        let er_path = limb_dir.join("eval_rot_key.bin");

        // `let_cxx_string!` expects something like `String` or `&str` (AsRef<[u8]>).
        // `to_string_lossy()` returns `Cow<str>` which doesn't implement AsRef<[u8]>.
        let cc_s_owned = cc_path.to_string_lossy().into_owned();
        let pk_s_owned = pk_path.to_string_lossy().into_owned();
        let sk_s_owned = sk_path.to_string_lossy().into_owned();
        let em_s_owned = em_path.to_string_lossy().into_owned();
        let er_s_owned = er_path.to_string_lossy().into_owned();

        // Use &str to avoid moving the owned `String` values (we reuse them later for parallel setup).
        let_cxx_string!(cc_s = cc_s_owned.as_str());
        let_cxx_string!(pk_s = pk_s_owned.as_str());
        let_cxx_string!(sk_s = sk_s_owned.as_str());
        let_cxx_string!(em_s = em_s_owned.as_str());
        let_cxx_string!(er_s = er_s_owned.as_str());

        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializeCryptoContextToFile(&cc_s, &cc, serial_mode_enum),
            "serialize crypto context failed"
        );
        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializePublicKeyToFile(&pk_s, &kp.GetPublicKey(), serial_mode_enum),
            "serialize public key failed"
        );
        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializePrivateKeyToFile(&sk_s, &kp.GetPrivateKey(), serial_mode_enum),
            "serialize private key failed"
        );
        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializeEvalMultKeyToFile(&em_s, &cc, serial_mode_enum),
            "serialize eval mult key failed"
        );
        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializeEvalAutomorphismKeyToFile(&er_s, &cc, serial_mode_enum),
            "serialize eval rot key failed"
        );

        // Basis ciphertexts ctK[j,b,ℓ] = Enc_pk( random vec in Z_t^B ) (v0).
        //
        // Stored in chunk files: basis/l{limb}/j{j}/blocks_{start}_{end}.bin
        // Each chunk file is a concatenation of serialized Ciphertext objects (same SerialMode),
        // so decap can read strictly streaming.
        let shape_stub = ShapeBlobManifestV0 {
            version: 0,
            shape_id: args.shape_id.clone(),
            n_armers: args.n_armers,
            s_basis: args.s_basis,
            d_limbs: args.d_limbs,
            moduli: args.moduli.clone(),
            epoch: args.epoch,
            slot_count: args.slot_count,
            block_count: args.block_count,
            blocks_per_chunk: args.blocks_per_chunk,
            required_rotations: rotations_powers_of_two(args.slot_count),
            weights_kind: args.weights_kind,
            ciphertext_encoding_version: 0,
            openfhe: None,
        };

        // Create directories first (avoid parallel mkdir races).
        for j in 0..args.s_basis {
            fs::create_dir_all(args.out_dir.join(format!("basis/l{limb}/j{j}"))).ok();
        }

        // Basis generation across j.
        //
        // Default: sequential (safe). Optional: parallel across `j` (faster on large servers),
        // but some OpenFHE builds may segfault under heavy concurrency. Use with care.
        let cc_path_s = Arc::new(cc_s_owned.clone());
        let pk_path_s = Arc::new(pk_s_owned.clone());
        let serial_mode_enum2 = serial_mode_enum;

        let gen_one_j = |j: usize| -> Result<()> {
            // Thread-local OpenFHE objects (do not share pointers across threads).
            let ctx = OpenFheBackend::deserialize_crypto_context(&cc_path_s, serial_mode_enum2)?;
            let pk = OpenFheBackend::deserialize_public_key(&pk_path_s, serial_mode_enum2)?;

            let mut start = 0usize;
            let mut rng = OsRng;
            while start < args.block_count {
                let end = (start + args.blocks_per_chunk).min(args.block_count);
                let ct_path = shape_stub.basis_chunk_path(&args.out_dir, limb, j, start, end);
                let ct_path_s = ct_path.to_string_lossy().into_owned();
                let mut writer = CtChunkWriter::create(&ct_path_s, serial_mode_enum)?;

                for _b in start..end {
                    let mut vec_i64 = CxxVector::<i64>::new();
                    for _ in 0..args.slot_count {
                        vec_i64.pin_mut().push((rng.next_u64() % pt_mod) as i64);
                    }
                    let pt = ctx.cc.MakePackedPlaintext(&vec_i64, 1, 0);
                    let ct = ctx.cc.EncryptByPublicKey(&pk.pk, &pt);
                    writer.append(&ct).with_context(|| {
                        format!("append basis ciphertext failed: {}", ct_path.display())
                    })?;
                }
                start = end;
            }
            Ok(())
        };

        if args.basis_parallelism == 1 {
            for j in 0..args.s_basis {
                gen_one_j(j)?;
            }
        } else {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(args.basis_parallelism)
                .build()
                .context("build rayon threadpool for basis generation")?;
            pool.install(|| (0..args.s_basis).into_par_iter().try_for_each(gen_one_j))?;
        }

        limb_files.push(OpenFheLimbFilesV0 {
            limb,
            plaintext_modulus: pt_mod,
            crypto_context_path: format!("openfhe/l{limb}/crypto_context.bin"),
            public_key_path: format!("openfhe/l{limb}/public_key.bin"),
            private_key_path: format!("openfhe/l{limb}/private_key.bin"),
            eval_mult_key_path: format!("openfhe/l{limb}/eval_mult_key.bin"),
            eval_rot_key_path: format!("openfhe/l{limb}/eval_rot_key.bin"),
        });
    }

    let manifest = ShapeBlobManifestV0 {
        version: 0,
        shape_id: args.shape_id,
        n_armers: args.n_armers,
        s_basis: args.s_basis,
        d_limbs: args.d_limbs,
        moduli: args.moduli,
        epoch: args.epoch,
        slot_count: args.slot_count,
        block_count: args.block_count,
        blocks_per_chunk: args.blocks_per_chunk,
        required_rotations: rotations_powers_of_two(args.slot_count),
        weights_kind: args.weights_kind,
        ciphertext_encoding_version: 0,
        openfhe: Some(OpenFheManifestV0 {
            version: 0,
            scheme: "BFVRNS".to_string(),
            multiplicative_depth: args.multiplicative_depth,
            serial_mode: args.serial_mode.to_ascii_uppercase(),
            limbs: limb_files,
        }),
    };

    let bytes = serde_json::to_vec_pretty(&manifest)?;
    fs::write(args.out_dir.join("manifest.json"), bytes)?;
    Ok(())
}

