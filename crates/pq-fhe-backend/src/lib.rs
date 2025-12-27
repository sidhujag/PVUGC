use anyhow::Result;

/// Narrow backend trait for GPT-Pro's "EvalTag(x,π)" public evaluator.
///
/// This is intentionally minimal: packed plaintext vectors, ct×pt, ct+ct, rotations, decrypt.
pub trait FheBackend {
    type Context;
    type PublicKey;
    type PrivateKey;
    type Ciphertext;
    type Plaintext;

    fn make_packed_plaintext(ctx: &Self::Context, values: &[i64]) -> Result<Self::Plaintext>;
    fn encrypt(ctx: &Self::Context, pk: &Self::PublicKey, pt: &Self::Plaintext) -> Result<Self::Ciphertext>;
    fn eval_mult_plain(ctx: &Self::Context, ct: &Self::Ciphertext, pt: &Self::Plaintext) -> Result<Self::Ciphertext>;
    fn eval_add(ctx: &Self::Context, a: &Self::Ciphertext, b: &Self::Ciphertext) -> Result<Self::Ciphertext>;
    fn eval_add_plain(ctx: &Self::Context, a: &Self::Ciphertext, pt: &Self::Plaintext) -> Result<Self::Ciphertext>;
    fn eval_rotate(ctx: &Self::Context, ct: &Self::Ciphertext, shift: i32) -> Result<Self::Ciphertext>;

    /// Decrypt and return packed values (length must already be set by caller/ctx policy).
    fn decrypt(ctx: &Self::Context, sk: &Self::PrivateKey, ct: &Self::Ciphertext) -> Result<Vec<i64>>;
}

