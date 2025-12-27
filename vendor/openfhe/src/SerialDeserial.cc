#include "SerialDeserial.h"

#include "openfhe/pke/cryptocontext-ser.h"
// OpenFHE 1.4.x does not automatically include cereal registrations for key types.
// Without this, SerializeEval*Key can throw "Trying to save an unregistered polymorphic type".
#include "openfhe/pke/key/key-ser.h"

#include "Ciphertext.h"
#include "CryptoContext.h"
#include "PrivateKey.h"
#include "PublicKey.h"

#include <utility>
#include <fstream>

namespace openfhe
{

template <typename ST, typename Object>
[[nodiscard]] bool SerialDeserial(const std::string& location,
    bool (* const funcPtr) (const std::string&, Object&, const ST&), Object& object)
{
    return funcPtr(location, object, ST{});
}
template <typename Object>
[[nodiscard]] bool Deserial(const std::string& location, Object& object,
    const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        return SerialDeserial<lbcrypto::SerType::SERBINARY, decltype(object.GetRef())>(location,
            lbcrypto::Serial::DeserializeFromFile, object.GetRef());
    }
    if (serialMode == SerialMode::JSON)
    {
        return SerialDeserial<lbcrypto::SerType::SERJSON, decltype(object.GetRef())>(location,
            lbcrypto::Serial::DeserializeFromFile, object.GetRef());
    }
    return false;
}
template <typename Object>
[[nodiscard]] bool Serial(const std::string& location, Object& object, const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        return SerialDeserial<lbcrypto::SerType::SERBINARY, decltype(object.GetRef())>(location,
            lbcrypto::Serial::SerializeToFile, object.GetRef());
    }
    if (serialMode == SerialMode::JSON)
    {
        return SerialDeserial<lbcrypto::SerType::SERJSON, decltype(object.GetRef())>(location,
            lbcrypto::Serial::SerializeToFile, object.GetRef());
    }
    return false;
}

template <typename ST, typename Stream, typename FStream, typename... Types>
[[nodiscard]] bool SerialDeserial(const std::string& location,
    bool (* const funcPtr) (Stream&, const ST&, Types... args), Types&&... args)
{
    const auto close = [](FStream* const fs){ if (fs->is_open()) { fs->close(); } };
    const std::unique_ptr<FStream, decltype(close)> fs(
        new FStream(location, std::ios::binary), close);
    return fs->is_open() ? funcPtr(*fs, ST{}, std::forward<Types>(args)...) : false;
}

// Ciphertext
bool DCRTPolyDeserializeCiphertextFromFile(const std::string& ciphertextLocation,
    CiphertextDCRTPoly& ciphertext, const SerialMode serialMode)
{
    return Deserial(ciphertextLocation, ciphertext, serialMode);
}
bool DCRTPolySerializeCiphertextToFile(const std::string& ciphertextLocation,
    const CiphertextDCRTPoly& ciphertext, const SerialMode serialMode)
{
    return Serial(ciphertextLocation, ciphertext, serialMode);
}

std::unique_ptr<CiphertextStreamReaderDCRTPoly> DCRTPolyNewCiphertextStreamReader(
    const std::string& path, const SerialMode serialMode)
{
    return std::make_unique<CiphertextStreamReaderDCRTPoly>(path, serialMode);
}

std::unique_ptr<CiphertextStreamWriterDCRTPoly> DCRTPolyNewCiphertextStreamWriter(
    const std::string& path, const SerialMode serialMode, const bool truncate)
{
    return std::make_unique<CiphertextStreamWriterDCRTPoly>(path, serialMode, truncate);
}

CiphertextStreamReaderDCRTPoly::CiphertextStreamReaderDCRTPoly(const std::string& path, const SerialMode mode)
    : m_in(path, std::ios::binary), m_mode(mode)
{ }

std::unique_ptr<CiphertextDCRTPoly> CiphertextStreamReaderDCRTPoly::Next()
{
    if (!m_in.is_open() || m_in.eof()) {
        return nullptr;
    }
    try {
        std::shared_ptr<CiphertextImpl> ct;
        if (m_mode == SerialMode::BINARY) {
            lbcrypto::Serial::Deserialize(ct, m_in, lbcrypto::SerType::SERBINARY{});
        }
        else if (m_mode == SerialMode::JSON) {
            lbcrypto::Serial::Deserialize(ct, m_in, lbcrypto::SerType::SERJSON{});
        }
        else {
            return nullptr;
        }
        if (!ct) {
            return nullptr;
        }
        return std::make_unique<CiphertextDCRTPoly>(std::move(ct));
    }
    catch (...) {
        return nullptr;
    }
}

CiphertextStreamWriterDCRTPoly::CiphertextStreamWriterDCRTPoly(const std::string& path, const SerialMode mode, const bool truncate)
    : m_out(path, std::ios::binary | (truncate ? std::ios::trunc : std::ios::app)), m_mode(mode)
{ }

bool CiphertextStreamWriterDCRTPoly::Append(const CiphertextDCRTPoly& ciphertext)
{
    if (!m_out.is_open()) {
        return false;
    }
    try {
        if (m_mode == SerialMode::BINARY) {
            lbcrypto::Serial::Serialize(ciphertext.GetRef(), m_out, lbcrypto::SerType::SERBINARY{});
            return true;
        }
        if (m_mode == SerialMode::JSON) {
            lbcrypto::Serial::Serialize(ciphertext.GetRef(), m_out, lbcrypto::SerType::SERJSON{});
            return true;
        }
        return false;
    }
    catch (...) {
        return false;
    }
}

// CryptoContext
bool DCRTPolyDeserializeCryptoContextFromFile(const std::string& ccLocation,
    CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode)
{
    return Deserial(ccLocation, cryptoContext, serialMode);
}
bool DCRTPolySerializeCryptoContextToFile(const std::string& ccLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode)
{
    return Serial(ccLocation, cryptoContext, serialMode);
}

// EvalAutomorphismKey
bool DCRTPolyDeserializeEvalAutomorphismKeyFromFile(const std::string& automorphismKeyLocation,
    const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        auto fn = static_cast<bool (*)(std::istream&, const lbcrypto::SerType::SERBINARY&)>(
            &CryptoContextImpl::DeserializeEvalAutomorphismKey<lbcrypto::SerType::SERBINARY>);
        return SerialDeserial<lbcrypto::SerType::SERBINARY, std::istream, std::ifstream>(
            automorphismKeyLocation, fn);
    }
    if (serialMode == SerialMode::JSON)
    {
        auto fn = static_cast<bool (*)(std::istream&, const lbcrypto::SerType::SERJSON&)>(
            &CryptoContextImpl::DeserializeEvalAutomorphismKey<lbcrypto::SerType::SERJSON>);
        return SerialDeserial<lbcrypto::SerType::SERJSON, std::istream, std::ifstream>(
            automorphismKeyLocation, fn);
    }
    return false;
}
bool DCRTPolySerializeEvalAutomorphismKeyByIdToFile(const std::string& automorphismKeyLocation,
    const SerialMode serialMode, const std::string& id)
{
    if (serialMode == SerialMode::BINARY)
    {
        auto fn = static_cast<bool (*)(std::ostream&, const lbcrypto::SerType::SERBINARY&, const std::string&)>(
            &CryptoContextImpl::SerializeEvalAutomorphismKey<lbcrypto::SerType::SERBINARY>);
        return SerialDeserial<lbcrypto::SerType::SERBINARY, std::ostream, std::ofstream>(
            automorphismKeyLocation, fn, id);
    }
    if (serialMode == SerialMode::JSON)
    {
        auto fn = static_cast<bool (*)(std::ostream&, const lbcrypto::SerType::SERJSON&, const std::string&)>(
            &CryptoContextImpl::SerializeEvalAutomorphismKey<lbcrypto::SerType::SERJSON>);
        return SerialDeserial<lbcrypto::SerType::SERJSON, std::ostream, std::ofstream>(
            automorphismKeyLocation, fn, id);
    }
    return false;
}
bool DCRTPolySerializeEvalAutomorphismKeyToFile(const std::string& automorphismKeyLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        // OpenFHE >=1.4 makes this an overloaded/templated API; avoid function-pointer casts.
        std::ofstream fs(automorphismKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalAutomorphismKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{}, cryptoContext.GetRef());
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ofstream fs(automorphismKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalAutomorphismKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{}, cryptoContext.GetRef());
    }
    return false;
}

// EvalMultKey
bool DCRTPolyDeserializeEvalMultKeyFromFile(const std::string& multKeyLocation,
    const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ifstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::DeserializeEvalMultKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{});
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ifstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::DeserializeEvalMultKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{});
    }
    return false;
}
bool SerializeEvalMultKeyDCRTPolyByIdToFile(const std::string& multKeyLocation,
    const SerialMode serialMode, const std::string& id)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ofstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalMultKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{}, id);
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ofstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalMultKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{}, id);
    }
    return false;
}
bool DCRTPolySerializeEvalMultKeyToFile(const std::string& multKeyLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ofstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalMultKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{}, cryptoContext.GetRef());
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ofstream fs(multKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalMultKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{}, cryptoContext.GetRef());
    }
    return false;
}

// EvalSumKey
bool DCRTPolyDeserializeEvalSumKeyFromFile(const std::string& sumKeyLocation, const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ifstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::DeserializeEvalSumKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{});
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ifstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::DeserializeEvalSumKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{});
    }
    return false;
}
bool DCRTPolySerializeEvalSumKeyByIdToFile(const std::string& sumKeyLocation,
    const SerialMode serialMode, const std::string& id)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ofstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalSumKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{}, id);
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ofstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalSumKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{}, id);
    }
    return false;
}
bool DCRTPolySerializeEvalSumKeyToFile(const std::string& sumKeyLocation,
    const CryptoContextDCRTPoly& cryptoContext, const SerialMode serialMode)
{
    if (serialMode == SerialMode::BINARY)
    {
        std::ofstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalSumKey<lbcrypto::SerType::SERBINARY>(
            fs, lbcrypto::SerType::SERBINARY{}, cryptoContext.GetRef());
    }
    if (serialMode == SerialMode::JSON)
    {
        std::ofstream fs(sumKeyLocation, std::ios::binary);
        if (!fs.is_open())
            return false;
        return CryptoContextImpl::SerializeEvalSumKey<lbcrypto::SerType::SERJSON>(
            fs, lbcrypto::SerType::SERJSON{}, cryptoContext.GetRef());
    }
    return false;
}

// PublicKey
bool DCRTPolyDeserializePublicKeyFromFile(const std::string& publicKeyLocation,
    PublicKeyDCRTPoly& publicKey, const SerialMode serialMode)
{
    return Deserial(publicKeyLocation, publicKey, serialMode);
}
bool DCRTPolySerializePublicKeyToFile(const std::string& publicKeyLocation,
    const PublicKeyDCRTPoly& publicKey, const SerialMode serialMode)
{
    return Serial(publicKeyLocation, publicKey, serialMode);
}

// PrivateKey
bool DCRTPolyDeserializePrivateKeyFromFile(const std::string& privateKeyLocation,
    PrivateKeyDCRTPoly& privateKey, const SerialMode serialMode)
{
    return Deserial(privateKeyLocation, privateKey, serialMode);
}
bool DCRTPolySerializePrivateKeyToFile(const std::string& privateKeyLocation,
    const PrivateKeyDCRTPoly& privateKey, const SerialMode serialMode)
{
    return Serial(privateKeyLocation, privateKey, serialMode);
}

} // openfhe
