use anyhow::{anyhow, Context, Result};
use openfhe::ffi as openfhe_ffi;
use pq_fhe_backend::FheBackend;

use openfhe::cxx::{self, let_cxx_string, CxxVector};
use pq_basis_blob::{
    rotations_powers_of_two, OpenFheLimbFilesV0, OpenFheManifestV0, ShapeBlobManifestV0,
    WeightsKind,
};
use rand_core::{OsRng, RngCore};
use std::fs;
use std::io::Write;
use std::path::Path;
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

/// A simple (non-TFHE-specific) LWE sample representation.
///
/// This is intended to be the **gate boundary** object (Option B).
/// - modulus `q` is the coefficient modulus of a *single* RLWE tower (RNS prime).
/// - `a` is length N (ring dimension) and `b` is the LWE body.
#[derive(Clone, Debug)]
pub struct LweSampleU64 {
    pub q: u64,
    pub a: Vec<u64>,
    pub b: u64,
}

/// Reduce a BFV/BGVRNS ciphertext down to a single RNS tower in-place.
///
/// This is required for the Track-A "single-tower bridge" semantics:
/// BFV decoding is defined relative to the *current ciphertext modulus* Q. If a ciphertext still has
/// multiple towers (Q = Π q_i), then extracting a sample from one tower and decoding against q_i is
/// not generally correct. After modulus reduction to one tower, Q == q0 and per-tower decoding is meaningful.
pub fn modreduce_to_one_tower_in_place(ctx: &OpenFheCtx, ct: &mut OpenFheCt) -> Result<()> {
    let ct_ref = ct.ct.as_ref().ok_or_else(|| anyhow!("null OpenFHE ciphertext"))?;
    let mut towers = openfhe_ffi::DCRTPolyCiphertextElementNumTowers(ct_ref, 0);
    anyhow::ensure!(towers >= 1, "invalid ciphertext tower count {towers}");
    while towers > 1 {
        ctx.cc.ModReduceInPlace(ct.ct.pin_mut());
        let ct_ref = ct.ct.as_ref().ok_or_else(|| anyhow!("null OpenFHE ciphertext"))?;
        towers = openfhe_ffi::DCRTPolyCiphertextElementNumTowers(ct_ref, 0);
    }
    Ok(())
}

/// Parameters describing the *bridge* boundary between OpenFHE BFV/BGV and the gate LWE domain.
///
/// This is an interface-level struct; the actual KSK generation/evaluation will live in the TFHE crate.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BridgeKeyV0 {
    pub version: u32,
    /// Input dimension (RLWE ring dimension N).
    pub n_in: usize,
    /// Output (gate) LWE dimension.
    pub n_out: usize,
    /// Input modulus q (tower modulus) used for extraction.
    pub q_in: u64,
    /// Keyswitch decomposition base (e.g., 2^base_log).
    pub base_log: usize,
    /// Keyswitch level count.
    pub level_count: usize,
    /// Opaque KSK bytes (TFHE-compatible serialization, to be specified).
    pub ksk_bytes: Vec<u8>,
}

impl LweSampleU64 {
    /// Minimal binary serialization (v0) for passing the bridge output to later tooling.
    ///
    /// Format:
    /// - magic: b"LWE0"
    /// - q: u64 LE
    /// - n: u32 LE
    /// - b: u64 LE
    /// - a[0..n): u64 LE
    pub fn write_to_file(&self, path: &Path) -> Result<()> {
        let mut f = fs::File::create(path).with_context(|| format!("create {}", path.display()))?;
        f.write_all(b"LWE0")?;
        f.write_all(&self.q.to_le_bytes())?;
        let n_u32: u32 = self
            .a
            .len()
            .try_into()
            .map_err(|_| anyhow!("lwe a.len too large"))?;
        f.write_all(&n_u32.to_le_bytes())?;
        f.write_all(&self.b.to_le_bytes())?;
        for &x in &self.a {
            f.write_all(&x.to_le_bytes())?;
        }
        f.flush()?;
        Ok(())
    }
}

/// Extract an LWE sample corresponding to **coefficient 0** from a BFV/BGV ciphertext.
///
/// This uses the standard RLWE->LWE sample-extraction fact for R_q = Z_q[x]/(x^N + 1).
///
/// With RLWE decryption:
///   m(x) = c0(x) + c1(x)*s(x)
/// the coefficient-0 term is:
///   m0 = c0[0] + c1[0]*s[0] - Σ_{i=1..N-1} c1[i] * s[N-i]    (mod q)
///
/// Define the LWE mask vector `a` as:
/// - a[0] = c1[0]
/// - for i=1..N-1: a[i] = -c1[N-i] mod q
/// Then:
///   m0 = b + <a, s_coeff_vector> (mod q)
///
/// Returned sample:
/// - b := c0[0] (mod q)
/// - a as above (mod q)
///
/// NOTE: BFV plaintext decoding includes scaling/rounding (Δ≈q/t) across the *full* CRT basis; this
/// function is purely the RLWE sample extraction over a single tower modulus.
pub fn extract_lwe_coeff0_from_ciphertext_tower(
    ct: &OpenFheCt,
    tower_index: u32,
) -> Result<LweSampleU64> {
    let ct_ref = ct
        .ct
        .as_ref()
        .ok_or_else(|| anyhow!("null OpenFHE ciphertext"))?;
    let c0 = openfhe_ffi::DCRTPolyExtractCiphertextElementTowerCoeffs(ct_ref, 0, tower_index);
    let c1 = openfhe_ffi::DCRTPolyExtractCiphertextElementTowerCoeffs(ct_ref, 1, tower_index);
    anyhow::ensure!(c0.len() >= 2, "c0 extraction returned too few values");
    anyhow::ensure!(c1.len() == c0.len(), "c1 extraction len mismatch");
    let q = c0[0];
    anyhow::ensure!(c1[0] == q, "c1 modulus mismatch");

    let n = c0.len() - 1;
    let c0_coeffs = &c0[1..];
    let c1_coeffs = &c1[1..];

    let b = c0_coeffs[0] % q;

    let mut a = vec![0u64; n];
    a[0] = c1_coeffs[0] % q;
    for i in 1..n {
        let v = c1_coeffs[n - i] % q;
        a[i] = if v == 0 { 0 } else { q - v };
    }

    Ok(LweSampleU64 { q, a, b })
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

    pub fn deserialize_crypto_context(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<OpenFheCtx> {
        let mut cc = openfhe_ffi::DCRTPolyGenNullCryptoContext();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeCryptoContextFromFile(&p, cc.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize crypto context failed: {path}"));
        }
        Ok(OpenFheCtx { cc })
    }

    pub fn deserialize_public_key(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<OpenFhePk> {
        let mut pk = openfhe_ffi::DCRTPolyGenNullPublicKey();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializePublicKeyFromFile(&p, pk.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize public key failed: {path}"));
        }
        Ok(OpenFhePk { pk })
    }

    pub fn deserialize_private_key(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<OpenFheSk> {
        let mut sk = openfhe_ffi::DCRTPolyGenNullPrivateKey();
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializePrivateKeyFromFile(&p, sk.pin_mut(), serial_mode) {
            return Err(anyhow!("deserialize private key failed: {path}"));
        }
        Ok(OpenFheSk { sk })
    }

    pub fn deserialize_eval_mult_key(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<()> {
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeEvalMultKeyFromFile(&p, serial_mode) {
            return Err(anyhow!("deserialize eval mult key failed: {path}"));
        }
        Ok(())
    }

    pub fn deserialize_eval_rot_key(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<()> {
        let_cxx_string!(p = path);
        if !openfhe_ffi::DCRTPolyDeserializeEvalAutomorphismKeyFromFile(&p, serial_mode) {
            return Err(anyhow!("deserialize eval rot key failed: {path}"));
        }
        Ok(())
    }

    pub fn deserialize_ciphertext(
        path: &str,
        serial_mode: openfhe_ffi::SerialMode,
    ) -> Result<OpenFheCt> {
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

    fn encrypt(
        ctx: &Self::Context,
        pk: &Self::PublicKey,
        pt: &Self::Plaintext,
    ) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EncryptByPublicKey(&pk.pk, &pt.pt),
        })
    }

    fn eval_mult_plain(
        ctx: &Self::Context,
        ct: &Self::Ciphertext,
        pt: &Self::Plaintext,
    ) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalMultByCiphertextAndPlaintext(&ct.ct, &pt.pt),
        })
    }

    fn eval_add(
        ctx: &Self::Context,
        a: &Self::Ciphertext,
        b: &Self::Ciphertext,
    ) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalAddByCiphertexts(&a.ct, &b.ct),
        })
    }

    fn eval_add_plain(
        ctx: &Self::Context,
        a: &Self::Ciphertext,
        pt: &Self::Plaintext,
    ) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalAddByCiphertextAndPlaintext(&a.ct, &pt.pt),
        })
    }

    fn eval_rotate(
        ctx: &Self::Context,
        ct: &Self::Ciphertext,
        shift: i32,
    ) -> Result<Self::Ciphertext> {
        Ok(OpenFheCt {
            ct: ctx.cc.EvalRotate(&ct.ct, shift),
        })
    }

    fn decrypt(
        ctx: &Self::Context,
        sk: &Self::PrivateKey,
        ct: &Self::Ciphertext,
    ) -> Result<Vec<i64>> {
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
pub fn decrypt_packed_with_len(
    ctx: &OpenFheCtx,
    sk: &OpenFheSk,
    ct: &OpenFheCt,
    len: usize,
) -> Result<Vec<i64>> {
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

/// Sanity-check that the classic rotation-based SlotSum produces a **constant polynomial**,
/// so that the decrypted coefficient vector has `coef[0] == sum` and `coef[i>0] == 0`.
///
/// Also prints/returns some debug info useful for the BFV->LWE bridge:
/// - ciphertext tower modulus `q_i`
/// - first few coefficients of ct element 0 / tower 0 after forcing COEFFICIENT format
///
/// This is a correctness-only diagnostic tool; not part of the production protocol.
pub fn sanity_openfhe_slot_sum_constant_poly(
    slot_count: usize,
    plaintext_modulus: u64,
) -> Result<()> {
    anyhow::ensure!(
        slot_count.is_power_of_two(),
        "slot_count must be power-of-two for simple SlotSum"
    );
    anyhow::ensure!(slot_count >= 2, "slot_count must be >= 2");

    // Build a minimal BFVRNS context (in-memory).
    let mut cc_params = openfhe_ffi::GenParamsBFVRNS();
    cc_params.pin_mut().SetPlaintextModulus(plaintext_modulus);
    cc_params.pin_mut().SetMultiplicativeDepth(2);
    cc_params.pin_mut().SetBatchSize(slot_count as u32);
    // IMPORTANT: In BFV batching, the "native" slot capacity is ring_dim/2 for cyclotomic order 2*ring_dim.
    // Our production configuration uses slot_count == ring_dim/2 (e.g., slot_count=4096, ring_dim=8192).
    //
    // If slot_count is smaller than ring_dim/2 (e.g. 16 vs ring_dim=8192 for security), rotations do NOT
    // wrap within the first `slot_count` values, and the rotate+add loop will not yield an all-slots constant.
    let ring_dim = (slot_count as u32).next_power_of_two().max(8192);
    let max_slots = (ring_dim / 2) as usize;
    anyhow::ensure!(
        slot_count == max_slots,
        "sanity requires slot_count == ring_dim/2 (got slot_count={slot_count}, ring_dim={ring_dim}, ring_dim/2={max_slots}). Use --slot-count 4096."
    );
    cc_params.pin_mut().SetRingDim(ring_dim);
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

    let mut index_list = CxxVector::<i32>::new();
    for r in rotations_powers_of_two(slot_count) {
        index_list.pin_mut().push(r);
    }
    cc.EvalRotateKeyGen(
        &kp.GetPrivateKey(),
        &index_list,
        &openfhe_ffi::DCRTPolyGenNullPublicKey(),
    );

    let ctx = OpenFheCtx { cc };
    let pk = OpenFhePk {
        pk: kp.GetPublicKey(),
    };
    let sk = OpenFheSk {
        sk: kp.GetPrivateKey(),
    };

    // Encrypt a simple known vector: [1,2,3,...,slot_count]
    let mut v = Vec::with_capacity(slot_count);
    for i in 0..slot_count {
        v.push((i as i64) + 1);
    }
    let pt = OpenFheBackend::make_packed_plaintext(&ctx, &v)?;
    let mut ct = OpenFheBackend::encrypt(&ctx, &pk, &pt)?;

    // SlotSum via rotations (all-reduce): ct = ct + rot(ct, 2^k) for k=0..logB-1.
    for r in rotations_powers_of_two(slot_count) {
        let rot = OpenFheBackend::eval_rotate(&ctx, &ct, r)?;
        ct = OpenFheBackend::eval_add(&ctx, &ct, &rot)?;
    }

    // Decrypt and check slots.
    let mut pt_out = openfhe_ffi::GenNullPlainText();
    ctx.cc
        .DecryptByPrivateKeyAndCiphertext(&sk.sk, &ct.ct, pt_out.pin_mut());
    pt_out.SetLength(slot_count);
    let packed = pt_out.GetPackedValue();
    anyhow::ensure!(packed.len() == slot_count, "decrypted slot len mismatch");

    let sum_expected_i128: i128 = (slot_count as i128 * (slot_count as i128 + 1)) / 2;
    let t = plaintext_modulus as i128;
    let sum_expected_mod_t = ((sum_expected_i128 % t) + t) % t;

    for i in 0..packed.len() {
        let x = *packed.get(i).unwrap_or(&0) as i128;
        let x_mod_t = ((x % t) + t) % t;
        anyhow::ensure!(
            x_mod_t == sum_expected_mod_t,
            "slot[{i}] != expected sum mod t (got {x_mod_t}, want {sum_expected_mod_t})"
        );
    }

    // Exercise the new ciphertext tower coefficient shim (bridge prerequisite).
    let tower = 0u32;
    let elem0_t0 = openfhe_ffi::DCRTPolyExtractCiphertextElementTowerCoeffs(&ct.ct, 0, tower);
    anyhow::ensure!(elem0_t0.len() >= 2, "expected [q, coeffs..] from shim");
    let q = elem0_t0[0];
    let n = elem0_t0.len() - 1;
    anyhow::ensure!(
        n as u32 == ring_dim,
        "shim coeff len mismatch: got {n}, want ring_dim {ring_dim}"
    );
    eprintln!("openfhe_sanity: t={plaintext_modulus} slot_count={slot_count} ring_dim={ring_dim} tower_q={q}");
    eprintln!(
        "openfhe_sanity: ct.c0[tower0].coeff[0..8]={:?}",
        &elem0_t0[1..1 + core::cmp::min(8, n)]
    );

    // Debug-only: extract the secret-key polynomial and validate the coefficient-0 RLWE decryption relation.
    //
    // With RLWE decryption over R_q = Z_q[x]/(x^N + 1): m(x) = c0(x) + c1(x)*s(x).
    // For coefficient 0 specifically:
    //   (c1*s)_0 = c1[0]*s[0] - Σ_{i=1..N-1} c1[i] * s[N-i]   (mod q)
    // so:
    //   m0 = c0[0] + (c1*s)_0 (mod q), then reduce mod t.
    let sk_t0 = openfhe_ffi::DCRTPolyExtractPrivateKeyTowerCoeffs(&sk.sk, tower);
    anyhow::ensure!(sk_t0.len() == elem0_t0.len(), "sk coeff len mismatch");
    anyhow::ensure!(sk_t0[0] == q, "sk modulus mismatch");
    let c0_0 = elem0_t0[1];
    let c1_t0 = openfhe_ffi::DCRTPolyExtractCiphertextElementTowerCoeffs(&ct.ct, 1, tower);
    anyhow::ensure!(c1_t0.len() == elem0_t0.len(), "c1 coeff len mismatch");
    anyhow::ensure!(c1_t0[0] == q, "c1 modulus mismatch");

    // Compute coefficient-0 product in the x^N+1 negacyclic ring.
    let qq = q as u128;
    let mut prod0 = (c1_t0[1] as u128) * (sk_t0[1] as u128) % qq;
    for i in 1..n {
        let c1_i = c1_t0[1 + i] as u128;
        let s_nmi = sk_t0[1 + (n - i)] as u128;
        let term = (c1_i * s_nmi) % qq;
        // subtract term mod q
        prod0 = (prod0 + qq - term) % qq;
    }
    let acc = (c0_0 as u128 + prod0) % qq;
    // NOTE: In BFV, the message is embedded with a scaling factor Δ ≈ q/t, so the raw value
    // `acc = (c0 + c1*s)_0 (mod q)` is *not* expected to equal the plaintext coefficient mod t
    // without applying the BFV scaling/rounding step (which depends on the full CRT basis).
    //
    // We keep this as debug output only. The bridge correctness we care about is that we can
    // reliably extract (c0,c1) coefficients in COEFFICIENT form.
    let acc_mod_t = (acc % (plaintext_modulus as u128)) as u64;
    eprintln!(
        "openfhe_sanity: raw (c0+c1*s)_0 mod t = {acc_mod_t} (expected plaintext sum mod t = {})",
        sum_expected_mod_t
    );

    Ok(())
}

/// Must-pass bridge sanity test (per GPT-Pro):
///
/// 1) Build a BFV context with the same batching convention (slot_count == ring_dim/2).
/// 2) Encrypt a known vector, run the same SlotSum all-reduce used in production.
/// 3) Extract an RLWE->LWE sample (a,b) for coefficient 0 for a chosen tower.
/// 4) Using the extracted secret key coefficients for that same tower, compute:
///      phase = b + <a, s_coeff> (mod q)
///    and BFV-decode (approximately):
///      m_rec = round(phase * t / q) (mod t)
/// 5) Check m_rec == expected plaintext sum mod t.
///
/// This validates:
/// - ciphertext coefficient extraction is in COEFFICIENT form (inverse NTT was applied)
/// - the negacyclic mapping for (a,b) is consistent with OpenFHE's RLWE convention
/// - BFV scaling/rounding is handled consistently at the bridge boundary (at least per-tower)
pub fn sanity_openfhe_bridge_decode(
    slot_count: usize,
    plaintext_modulus: u64,
    tower_index: u32,
) -> Result<()> {
    anyhow::ensure!(
        slot_count.is_power_of_two(),
        "slot_count must be power-of-two for simple SlotSum"
    );
    anyhow::ensure!(slot_count >= 2, "slot_count must be >= 2");

    // Build a minimal BFVRNS context (in-memory), matching `sanity_openfhe_slot_sum_constant_poly`.
    let mut cc_params = openfhe_ffi::GenParamsBFVRNS();
    cc_params.pin_mut().SetPlaintextModulus(plaintext_modulus);
    cc_params.pin_mut().SetMultiplicativeDepth(2);
    cc_params.pin_mut().SetBatchSize(slot_count as u32);
    let ring_dim = (slot_count as u32).next_power_of_two().max(8192);
    let max_slots = (ring_dim / 2) as usize;
    anyhow::ensure!(
        slot_count == max_slots,
        "sanity requires slot_count == ring_dim/2 (got slot_count={slot_count}, ring_dim={ring_dim}, ring_dim/2={max_slots}). Use --slot-count 4096."
    );
    cc_params.pin_mut().SetRingDim(ring_dim);
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

    let mut index_list = CxxVector::<i32>::new();
    for r in rotations_powers_of_two(slot_count) {
        index_list.pin_mut().push(r);
    }
    cc.EvalRotateKeyGen(
        &kp.GetPrivateKey(),
        &index_list,
        &openfhe_ffi::DCRTPolyGenNullPublicKey(),
    );

    let ctx = OpenFheCtx { cc };
    let pk = OpenFhePk {
        pk: kp.GetPublicKey(),
    };
    let sk = OpenFheSk {
        sk: kp.GetPrivateKey(),
    };

    // Encrypt a known vector [1,2,3,...,slot_count] so SlotSum target is deterministic.
    let mut v = Vec::with_capacity(slot_count);
    for i in 0..slot_count {
        v.push((i as i64) + 1);
    }
    let pt = OpenFheBackend::make_packed_plaintext(&ctx, &v)?;
    let mut ct = OpenFheBackend::encrypt(&ctx, &pk, &pt)?;

    // SlotSum via rotations (all-reduce): ct = ct + rot(ct, 2^k).
    for r in rotations_powers_of_two(slot_count) {
        let rot = OpenFheBackend::eval_rotate(&ctx, &ct, r)?;
        ct = OpenFheBackend::eval_add(&ctx, &ct, &rot)?;
    }

    // IMPORTANT (Bridge semantics):
    //
    // OpenFHE BFVRNS ciphertexts live over a *composite* ciphertext modulus Q = Π q_i (RNS primes).
    // If we naively extract coefficients from one tower q_i while the ciphertext still has other towers,
    // the BFV Δ scaling is with respect to Q, not q_i, and a per-tower decode
    //   round(phase * t / q_i)
    // will generally fail.
    //
    // For the stream->gate bridge, we therefore first reduce the ciphertext modulus down to a
    // single RNS prime (so Q == q0), and then extract tower 0.
    //
    // This test enforces that convention. (Production bridge code should follow the same rule.)
    if tower_index != 0 {
        return Err(anyhow!(
            "openfhe_sanity_bridge: tower_index must be 0 after modulus reduction to one tower (got {tower_index})"
        ));
    }

    // Reduce modulus until only one tower remains (Q == q0).
    loop {
        let ct_ref = ct
            .ct
            .as_ref()
            .ok_or_else(|| anyhow!("null OpenFHE ciphertext"))?;
        let towers = openfhe_ffi::DCRTPolyCiphertextElementNumTowers(ct_ref, 0);
        anyhow::ensure!(towers >= 1, "invalid ciphertext tower count {towers}");
        if towers == 1 {
            break;
        }
        // Drop one RNS prime (OpenFHE performs the appropriate modulus reduction).
        ctx.cc.ModReduceInPlace(ct.ct.pin_mut());
    }

    // Expected message (mod t).
    let sum_expected_i128: i128 = (slot_count as i128 * (slot_count as i128 + 1)) / 2;
    let t_i128 = plaintext_modulus as i128;
    let sum_expected_mod_t = ((sum_expected_i128 % t_i128) + t_i128) % t_i128;

    // Decrypt as OpenFHE sees it (ground truth check).
    let slots = decrypt_packed_with_len(&ctx, &sk, &ct, slot_count)?;
    for (i, &x) in slots.iter().enumerate() {
        let x_mod_t = ((x as i128 % t_i128) + t_i128) % t_i128;
        anyhow::ensure!(
            x_mod_t == sum_expected_mod_t,
            "openfhe_sanity_bridge: decrypted slot[{i}] != expected sum mod t (got {x_mod_t}, want {sum_expected_mod_t})"
        );
    }

    // Bridge extraction (a,b) at coefficient 0 (single-tower).
    let lwe = extract_lwe_coeff0_from_ciphertext_tower(&ct, 0)?;
    let q = lwe.q as i128;
    anyhow::ensure!(q > 2, "invalid tower modulus q={}", lwe.q);

    // Extract secret key coefficients for this tower (debug-only shim; required for this sanity test).
    let sk_t = openfhe_ffi::DCRTPolyExtractPrivateKeyTowerCoeffs(&sk.sk, tower_index);
    anyhow::ensure!(
        sk_t.len() >= 2,
        "sk coeff extraction returned too few values"
    );
    anyhow::ensure!(
        sk_t[0] == lwe.q,
        "sk modulus mismatch (sk_q={}, lwe_q={})",
        sk_t[0],
        lwe.q
    );
    let s_coeffs = &sk_t[1..];
    anyhow::ensure!(
        s_coeffs.len() == lwe.a.len(),
        "sk coeff len mismatch (got {}, want {})",
        s_coeffs.len(),
        lwe.a.len()
    );

    // phase = b + <a, s> (mod q)
    let qq = lwe.q as u128;
    let mut ip: u128 = 0;
    for (ai, si) in lwe.a.iter().zip(s_coeffs.iter()) {
        ip = (ip + (*ai as u128) * (*si as u128)) % qq;
    }
    let phase_u = ((lwe.b as u128) + ip) % qq;

    // Decode per-tower: m_rec = round(phase * t / q) mod t.
    //
    // Use a centered representative to make rounding meaningful.
    let mut phase_centered: i128 = phase_u as i128;
    if phase_centered > q / 2 {
        phase_centered -= q;
    }

    // nearest integer rounding of (phase_centered * t / q)
    let num: i128 = phase_centered * t_i128;
    let half_q: i128 = q / 2;
    let m_rec_i128: i128 = if num >= 0 {
        (num + half_q) / q
    } else {
        (num - half_q) / q
    };
    let m_rec_mod_t = ((m_rec_i128 % t_i128) + t_i128) % t_i128;
    let m_rec_byte = (m_rec_mod_t as u64) & 0xff;
    let expected_byte = (sum_expected_mod_t as u64) & 0xff;

    anyhow::ensure!(
        m_rec_mod_t == sum_expected_mod_t,
        "openfhe_sanity_bridge: BFV decode from extracted (a,b) failed (tower={tower_index}): got {m_rec_mod_t}, want {sum_expected_mod_t}"
    );

    eprintln!(
        "openfhe_sanity_bridge: OK (tower={tower_index}) q={} t={} expected={} (byte={:02x}) phase_centered={} m_rec={} (byte={:02x})",
        lwe.q, plaintext_modulus, sum_expected_mod_t, expected_byte, phase_centered, m_rec_mod_t, m_rec_byte
    );
    Ok(())
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
    /// If true, reuse a single basis (and OpenFHE key material) across all limbs.
    pub basis_shared_across_limbs: bool,
    /// If true, derive weights with an explicit limb domain separator.
    pub weights_domain_sep_per_limb: bool,
    pub multiplicative_depth: u32,
    pub serial_mode: String,
    /// Parallelism for basis ciphertext generation across `j`.
    ///
    /// IMPORTANT: Some OpenFHE builds appear not to be fully thread-safe for (de)serialization +
    /// encryption in parallel. Default is 1 (safe). Increase cautiously (e.g. 8/16) on servers.
    pub basis_parallelism: usize,
}

/// Multi-process worker: generate basis ciphertexts for a limb and a basis-index range `[j_start, j_end)`.
///
/// This reads `manifest.json` for parameters and uses the already-written OpenFHE artifacts in
/// `openfhe/l{limb}/`.
pub fn openfhe_generate_basis_worker(
    shape_blob_dir: &PathBuf,
    limb: usize,
    j_start: usize,
    j_end: usize,
) -> Result<()> {
    anyhow::ensure!(j_start <= j_end, "invalid j range");

    let manifest_path = shape_blob_dir.join("manifest.json");
    let manifest_bytes =
        fs::read(&manifest_path).with_context(|| format!("read {}", manifest_path.display()))?;
    let m: ShapeBlobManifestV0 =
        serde_json::from_slice(&manifest_bytes).context("parse manifest.json")?;
    anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);

    if m.basis_shared_across_limbs && limb != 0 {
        // Shared basis mode: only limb 0 has distinct basis material on disk.
        // Higher limbs are mapped to limb 0 by `ShapeBlobManifestV0::basis_chunk_path`.
        return Ok(());
    }
    let of = m
        .openfhe
        .clone()
        .ok_or_else(|| anyhow!("manifest missing openfhe section"))?;
    let serial_mode_enum = OpenFheBackend::parse_serial_mode(&of.serial_mode)?;

    let limb_idx = if m.basis_shared_across_limbs { 0 } else { limb };
    let limb_cfg = of
        .limbs
        .iter()
        .find(|x| x.limb == limb_idx)
        .ok_or_else(|| anyhow!("missing openfhe limb {limb_idx}"))?
        .clone();
    let pt_mod = limb_cfg.plaintext_modulus;

    // Deserialize the OpenFHE context + public key for this limb (process-local).
    let ctx = OpenFheBackend::deserialize_crypto_context(
        shape_blob_dir
            .join(&limb_cfg.crypto_context_path)
            .to_string_lossy()
            .as_ref(),
        serial_mode_enum,
    )?;
    let pk = OpenFheBackend::deserialize_public_key(
        shape_blob_dir
            .join(&limb_cfg.public_key_path)
            .to_string_lossy()
            .as_ref(),
        serial_mode_enum,
    )?;

    // Ensure basis directories exist (shared-basis mode writes only under l0).
    let basis_limb = if m.basis_shared_across_limbs { 0 } else { limb };
    for j in j_start..j_end {
        fs::create_dir_all(shape_blob_dir.join(format!("basis/l{basis_limb}/j{j}"))).ok();
    }

    let mut rng = OsRng;
    for j in j_start..j_end {
        let mut start = 0usize;
        while start < m.block_count {
            let end = (start + m.blocks_per_chunk).min(m.block_count);
            let ct_path = m.basis_chunk_path(shape_blob_dir, limb, j, start, end);
            let ct_path_s = ct_path.to_string_lossy().into_owned();
            let mut writer = CtChunkWriter::create(&ct_path_s, serial_mode_enum)?;

            for _b in start..end {
                let mut vec_i64 = CxxVector::<i64>::new();
                for _ in 0..m.slot_count {
                    vec_i64.pin_mut().push((rng.next_u64() % pt_mod) as i64);
                }
                let pt = ctx.cc.MakePackedPlaintext(&vec_i64, 1, 0);
                let ct = ctx.cc.EncryptByPublicKey(&pk.pk, &pt);
                writer.append(&ct).with_context(|| {
                    format!("append basis ciphertext failed: {}", ct_path.display())
                })?;
            }
            drop(writer);
            start = end;
        }
    }

    Ok(())
}

/// Keys-only OpenFHE setup: writes `manifest.json` + OpenFHE artifacts, but does **not** generate basis ciphertexts.
pub fn setup_shape_blob_openfhe_keys_only(args: &SetupShapeBlobArgs) -> Result<()> {
    anyhow::ensure!(args.blocks_per_chunk > 0, "blocks_per_chunk must be > 0");
    anyhow::ensure!(
        args.moduli.len() == args.d_limbs,
        "moduli.len must equal d_limbs"
    );
    let serial_mode_enum = OpenFheBackend::parse_serial_mode(&args.serial_mode)?;

    fs::create_dir_all(&args.out_dir)?;
    fs::create_dir_all(args.out_dir.join("basis")).ok();
    fs::create_dir_all(args.out_dir.join("openfhe")).ok();

    let mut limb_files: Vec<OpenFheLimbFilesV0> = Vec::new();

    if args.basis_shared_across_limbs {
        // Shared basis + shared OpenFHE keys require identical plaintext modulus across limbs.
        anyhow::ensure!(
            args.moduli.iter().all(|&x| x == args.moduli[0]),
            "basis_shared_across_limbs requires all moduli identical"
        );
    }

    let limbs_to_build: Vec<(usize, u64)> = if args.basis_shared_across_limbs {
        vec![(0usize, args.moduli[0])]
    } else {
        args.moduli.iter().copied().enumerate().collect()
    };

    for (limb, pt_mod) in limbs_to_build.into_iter() {
        let limb_dir = args.out_dir.join(format!("openfhe/l{limb}"));
        fs::create_dir_all(&limb_dir).ok();

        let mut cc_params = openfhe_ffi::GenParamsBFVRNS();
        cc_params.pin_mut().SetPlaintextModulus(pt_mod);
        cc_params
            .pin_mut()
            .SetMultiplicativeDepth(args.multiplicative_depth);
        cc_params.pin_mut().SetBatchSize(args.slot_count as u32);
        let ring_dim = (args.slot_count as u32).next_power_of_two().max(8192);
        cc_params.pin_mut().SetRingDim(ring_dim);
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

        let mut index_list = CxxVector::<i32>::new();
        for r in rotations_powers_of_two(args.slot_count) {
            index_list.pin_mut().push(r);
        }
        cc.EvalRotateKeyGen(
            &kp.GetPrivateKey(),
            &index_list,
            &openfhe_ffi::DCRTPolyGenNullPublicKey(),
        );

        let cc_path = limb_dir.join("crypto_context.bin");
        let pk_path = limb_dir.join("public_key.bin");
        let sk_path = limb_dir.join("private_key.bin");
        let em_path = limb_dir.join("eval_mult_key.bin");
        let er_path = limb_dir.join("eval_rot_key.bin");

        let cc_s_owned = cc_path.to_string_lossy().into_owned();
        let pk_s_owned = pk_path.to_string_lossy().into_owned();
        let sk_s_owned = sk_path.to_string_lossy().into_owned();
        let em_s_owned = em_path.to_string_lossy().into_owned();
        let er_s_owned = er_path.to_string_lossy().into_owned();

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
            openfhe_ffi::DCRTPolySerializePublicKeyToFile(
                &pk_s,
                &kp.GetPublicKey(),
                serial_mode_enum
            ),
            "serialize public key failed"
        );
        anyhow::ensure!(
            openfhe_ffi::DCRTPolySerializePrivateKeyToFile(
                &sk_s,
                &kp.GetPrivateKey(),
                serial_mode_enum
            ),
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

        // Ensure basis directories exist (shared-basis mode writes only under l0).
        let basis_limb = if args.basis_shared_across_limbs { 0 } else { limb };
        for j in 0..args.s_basis {
            fs::create_dir_all(args.out_dir.join(format!("basis/l{basis_limb}/j{j}"))).ok();
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
        basis_shared_across_limbs: args.basis_shared_across_limbs,
        weights_domain_sep_per_limb: args.weights_domain_sep_per_limb,
        ciphertext_encoding_version: 0,
        openfhe: Some(OpenFheManifestV0 {
            version: 0,
            scheme: "BFVRNS".to_string(),
            multiplicative_depth: args.multiplicative_depth,
            serial_mode: args.serial_mode.to_ascii_uppercase(),
            limbs: limb_files,
        }),
        bridge: None,
    };

    let manifest_path = args.out_dir.join("manifest.json");
    let manifest_bytes = serde_json::to_vec_pretty(&manifest)?;
    fs::write(&manifest_path, manifest_bytes)
        .with_context(|| format!("write {}", manifest_path.display()))?;

    Ok(())
}

pub fn setup_shape_blob_openfhe(args: SetupShapeBlobArgs) -> Result<()> {
    anyhow::ensure!(args.blocks_per_chunk > 0, "blocks_per_chunk must be > 0");
    anyhow::ensure!(
        args.moduli.len() == args.d_limbs,
        "moduli.len must equal d_limbs"
    );
    anyhow::ensure!(
        args.basis_parallelism == 1,
        "threaded OpenFHE setup is disabled; use pvugc_pq multiprocess when basis_parallelism>1"
    );
    setup_shape_blob_openfhe_keys_only(&args)?;
    // Sequential basis generation inside this process.
    if args.basis_shared_across_limbs {
        openfhe_generate_basis_worker(&args.out_dir, 0, 0, args.s_basis)?;
    } else {
        for limb in 0..args.d_limbs {
            openfhe_generate_basis_worker(&args.out_dir, limb, 0, args.s_basis)?;
        }
    }
    Ok(())
}
