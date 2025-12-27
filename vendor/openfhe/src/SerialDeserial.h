#pragma once

#include "SerialMode.h"

#include <fstream>
#include <memory>
#include <string>
#include <vector>

namespace openfhe
{

class CiphertextDCRTPoly;
class CryptoContextDCRTPoly;
class PublicKeyDCRTPoly;
class PrivateKeyDCRTPoly;

// Chunked ciphertext streaming (for huge basis blobs).
//
// We store a chunk file as a concatenation of serialized Ciphertext objects (same SerialMode),
// and read/write them sequentially. This avoids millions of tiny files while keeping decap strictly
// streaming.
class CiphertextStreamReaderDCRTPoly;
class CiphertextStreamWriterDCRTPoly;

// Ciphertext
[[nodiscard]] bool DCRTPolyDeserializeCiphertextFromFile(const std::string& ciphertextLocation,
    CiphertextDCRTPoly& ciphertext, const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializeCiphertextToFile(const std::string& ciphertextLocation,
    const CiphertextDCRTPoly& ciphertext, const SerialMode serialMode);

// Chunked ciphertext stream helpers (sequential)
[[nodiscard]] std::unique_ptr<CiphertextStreamReaderDCRTPoly> DCRTPolyNewCiphertextStreamReader(
    const std::string& path, const SerialMode serialMode);
[[nodiscard]] std::unique_ptr<CiphertextStreamWriterDCRTPoly> DCRTPolyNewCiphertextStreamWriter(
    const std::string& path, const SerialMode serialMode, bool truncate);
// Same, but allow overriding the underlying std::fstream buffer size (in bytes).
// If bufferBytes == 0, uses the iostream default.
[[nodiscard]] std::unique_ptr<CiphertextStreamReaderDCRTPoly> DCRTPolyNewCiphertextStreamReaderWithBuffer(
    const std::string& path, const SerialMode serialMode, size_t bufferBytes);
[[nodiscard]] std::unique_ptr<CiphertextStreamWriterDCRTPoly> DCRTPolyNewCiphertextStreamWriterWithBuffer(
    const std::string& path, const SerialMode serialMode, bool truncate, size_t bufferBytes);

class CiphertextStreamReaderDCRTPoly final {
    std::ifstream m_in;
    SerialMode m_mode;
    std::vector<char> m_buf;
public:
    CiphertextStreamReaderDCRTPoly(const std::string& path, SerialMode mode);
    CiphertextStreamReaderDCRTPoly(const std::string& path, SerialMode mode, size_t bufferBytes);
    [[nodiscard]] std::unique_ptr<CiphertextDCRTPoly> Next();
};

class CiphertextStreamWriterDCRTPoly final {
    std::ofstream m_out;
    SerialMode m_mode;
    std::vector<char> m_buf;
public:
    CiphertextStreamWriterDCRTPoly(const std::string& path, SerialMode mode, bool truncate);
    CiphertextStreamWriterDCRTPoly(const std::string& path, SerialMode mode, bool truncate, size_t bufferBytes);
    [[nodiscard]] bool Append(const CiphertextDCRTPoly& ciphertext);
};

// CryptoContext
[[nodiscard]] bool DCRTPolyDeserializeCryptoContextFromFile(const std::string& ccLocation,
    CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializeCryptoContextToFile(const std::string& ccLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode);

// EvalAutomorphismKey
[[nodiscard]] bool DCRTPolyDeserializeEvalMultKeyFromFile(const std::string& multKeyLocation,
    const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializeEvalMultKeyByIdToFile(const std::string& multKeyLocation,
    const SerialMode serialMode, const std::string& id);
[[nodiscard]] bool DCRTPolySerializeEvalMultKeyToFile(const std::string& multKeyLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode);

// EvalMultKey
[[nodiscard]] bool DCRTPolyDeserializeEvalAutomorphismKeyFromFile(
    const std::string& automorphismKeyLocation, const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializeEvalAutomorphismKeyByIdToFile(
    const std::string& automorphismKeyLocation, const SerialMode serialMode,
    const std::string& id);
[[nodiscard]] bool DCRTPolySerializeEvalAutomorphismKeyToFile(
    const std::string& automorphismKeyLocation, const CryptoContextDCRTPoly& cryptoContext,
    const SerialMode serialMode);

// EvalSumKey
[[nodiscard]] bool DCRTPolyDeserializeEvalSumKeyFromFile(const std::string& sumKeyLocation,
    const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializeEvalSumKeyByIdToFile(const std::string& sumKeyLocation,
    const SerialMode serialMode, const std::string& id);
[[nodiscard]] bool DCRTPolySerializeEvalSumKeyToFile(const std::string& sumKeyLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode);

// PublicKey
[[nodiscard]] bool DCRTPolyDeserializePublicKeyFromFile(const std::string& publicKeyLocation,
    PublicKeyDCRTPoly& publicKey, const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializePublicKeyToFile(const std::string& publicKeyLocation,
    const PublicKeyDCRTPoly& publicKey, const SerialMode serialMode);

// PrivateKey (dev-only use: fake gate)
[[nodiscard]] bool DCRTPolyDeserializePrivateKeyFromFile(const std::string& privateKeyLocation,
    PrivateKeyDCRTPoly& privateKey, const SerialMode serialMode);
[[nodiscard]] bool DCRTPolySerializePrivateKeyToFile(const std::string& privateKeyLocation,
    const PrivateKeyDCRTPoly& privateKey, const SerialMode serialMode);

} // openfhe
