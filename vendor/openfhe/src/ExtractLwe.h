#pragma once

#include <cstdint>

#include "rust/cxx.h"

#include "openfhe/core/lattice/hal/lat-backend.h"
#include "openfhe/pke/ciphertext.h"
#include "openfhe/pke/key/privatekey.h"

#include "Ciphertext.h"
#include "PrivateKey.h"

namespace openfhe {

// Return the number of RNS towers (primes) in the specified ciphertext element.
//
// NOTE: This is needed on the Rust side to:
// - validate tower_index bounds (avoid uncaught OpenFHE exceptions crossing FFI),
// - drive ModReduce loops in bridge sanity tests.
[[nodiscard]] std::uint32_t DCRTPolyCiphertextElementNumTowers(
    const CiphertextDCRTPoly& ciphertext,
    std::uint32_t elementIndex);

// Extract coefficients of one tower (RNS prime) for one ciphertext element.
//
// IMPORTANT:
// - We force COEFFICIENT format (inverse NTT) before reading coefficients.
// - This returns coefficients mod the selected tower modulus.
//
// This is the first building block for the BFV/BGV -> (sample-extracted) LWE bridge.
//
// Return format:
// - out[0] = modulus (q_i)
// - out[1..] = coefficients (len = ring_dim)
[[nodiscard]] rust::Vec<std::uint64_t> DCRTPolyExtractCiphertextElementTowerCoeffs(
    const CiphertextDCRTPoly& ciphertext,
    std::uint32_t elementIndex,
    std::uint32_t towerIndex);

// Debug-only helper: extract the RLWE secret polynomial coefficients (one tower).
//
// This is ONLY for local sanity checks validating RLWE->LWE sample extraction math.
// Do NOT use this in production paths; the real system must never reveal the secret key.
//
// Return format:
// - out[0] = modulus (q_i)
// - out[1..] = coefficients (len = ring_dim)
[[nodiscard]] rust::Vec<std::uint64_t> DCRTPolyExtractPrivateKeyTowerCoeffs(
    const PrivateKeyDCRTPoly& privateKey,
    std::uint32_t towerIndex);

} // namespace openfhe

