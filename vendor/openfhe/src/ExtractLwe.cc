#include "ExtractLwe.h"

#include "openfhe/core/utils/exception.h"
#include "openfhe/pke/key/privatekey.h"

namespace openfhe {

std::uint32_t DCRTPolyCiphertextElementNumTowers(
    const CiphertextDCRTPoly& ciphertext,
    const std::uint32_t elementIndex) {
    const auto& ctPtr = ciphertext.GetRef();
    if (!ctPtr) {
        OPENFHE_THROW("ciphertext is null");
    }

    auto& elems = ctPtr->GetElements();
    if (elementIndex >= elems.size()) {
        OPENFHE_THROW("ciphertext elementIndex out of range");
    }

    lbcrypto::DCRTPoly& poly = elems[elementIndex];
    return static_cast<std::uint32_t>(poly.GetNumOfElements());
}

rust::Vec<std::uint64_t> DCRTPolyExtractCiphertextElementTowerCoeffs(
    const CiphertextDCRTPoly& ciphertext,
    const std::uint32_t elementIndex,
    const std::uint32_t towerIndex) {
    const auto& ctPtr = ciphertext.GetRef();
    if (!ctPtr) {
        OPENFHE_THROW("ciphertext is null");
    }

    auto& elems = ctPtr->GetElements();
    if (elementIndex >= elems.size()) {
        OPENFHE_THROW("ciphertext elementIndex out of range");
    }

    lbcrypto::DCRTPoly& poly = elems[elementIndex];

    // Force coefficient format (inverse NTT). This is required for meaningful coefficient extraction.
    poly.SetFormat(Format::COEFFICIENT);

    const auto numTowers = poly.GetNumOfElements();
    if (towerIndex >= numTowers) {
        OPENFHE_THROW("ciphertext towerIndex out of range");
    }

    const auto& tower = poly.GetElementAtIndex(towerIndex); // lbcrypto::NativePoly
    // Ensure tower is in coefficient form too.
    // (It should be after poly.SetFormat, but keep this explicit.)
    const_cast<lbcrypto::NativePoly&>(tower).SetFormat(Format::COEFFICIENT);

    rust::Vec<std::uint64_t> out;
    out.reserve(static_cast<std::size_t>(1 + tower.GetLength()));
    out.push_back(tower.GetModulus().ConvertToInt());

    const auto& v = tower.GetValues(); // lbcrypto::NativeVector
    const auto n = v.GetLength();
    for (usint i = 0; i < n; ++i) {
        out.push_back(v[i].ConvertToInt());
    }

    return out;
}

rust::Vec<std::uint64_t> DCRTPolyExtractPrivateKeyTowerCoeffs(
    const PrivateKeyDCRTPoly& privateKey,
    const std::uint32_t towerIndex) {
    const auto& skPtr = privateKey.GetRef();
    if (!skPtr) {
        OPENFHE_THROW("private key is null");
    }

    auto poly = skPtr->GetPrivateElement(); // DCRTPoly (copy)
    poly.SetFormat(Format::COEFFICIENT);

    const auto numTowers = poly.GetNumOfElements();
    if (towerIndex >= numTowers) {
        OPENFHE_THROW("private key towerIndex out of range");
    }

    const auto& tower = poly.GetElementAtIndex(towerIndex); // NativePoly
    const_cast<lbcrypto::NativePoly&>(tower).SetFormat(Format::COEFFICIENT);

    rust::Vec<std::uint64_t> out;
    out.reserve(static_cast<std::size_t>(1 + tower.GetLength()));
    out.push_back(tower.GetModulus().ConvertToInt());

    const auto& v = tower.GetValues();
    const auto n = v.GetLength();
    for (usint i = 0; i < n; ++i) {
        out.push_back(v[i].ConvertToInt());
    }
    return out;
}

} // namespace openfhe

