//! Canonical (hardened) serialization/deserialization helpers

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

/// Deserialize with canonical validation (Validate::Yes) from a byte slice
pub fn deserialize_canonical<T: CanonicalDeserialize>(
    bytes: &[u8],
) -> Result<T, ark_serialize::SerializationError> {
    let mut cursor = std::io::Cursor::new(bytes);
    T::deserialize_with_mode(&mut cursor, Compress::Yes, Validate::Yes)
}

/// Serialize to canonical compressed bytes
pub fn serialize_canonical<T: CanonicalSerialize>(
    value: &T,
) -> Result<Vec<u8>, ark_serialize::SerializationError> {
    let mut out = Vec::new();
    value.serialize_with_mode(&mut out, Compress::Yes)?;
    Ok(out)
}
