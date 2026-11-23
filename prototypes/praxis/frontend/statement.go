// Specialize an independently supplied, five-input gnark BN254 Groth16 key.
package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"slices"

	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	native "github.com/consensys/gnark/backend/groth16/bn254"
)

// The maximal uncompressed supported layout is nine G1s, three G2s, and
// three uint32 counters. Decode the dynamic sections element by element to
// avoid allocating a slice based on an attacker-controlled wire length.
const keyLimit = 9*curve.SizeOfG1AffineUncompressed + 3*curve.SizeOfG2AffineUncompressed + 12
const jsonLimit = 8192

func limitedBytes(r io.Reader, limit int64) ([]byte, error) {
	data, err := io.ReadAll(io.LimitReader(r, limit+1))
	if err != nil {
		return nil, err
	}
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("input exceeds %d bytes", limit)
	}
	return data, nil
}

func limitedFile(path string, limit int64) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	return limitedBytes(f, limit)
}

func parseKey(data []byte) (*native.VerifyingKey, [32]byte, error) {
	digest := sha256.Sum256(data)
	if len(data) > keyLimit {
		return nil, digest, fmt.Errorf("unexpected verification key length")
	}
	r := bytes.NewReader(data)
	dec := curve.NewDecoder(r) // includes curve and subgroup checks
	var vk native.VerifyingKey
	for _, p := range []any{&vk.G1.Alpha, &vk.G1.Beta, &vk.G2.Beta, &vk.G2.Gamma, &vk.G1.Delta, &vk.G2.Delta} {
		if err := dec.Decode(p); err != nil {
			return nil, digest, err
		}
	}
	var count uint32
	if err := binary.Read(r, binary.BigEndian, &count); err != nil {
		return nil, digest, err
	}
	if count != 6 {
		return nil, digest, fmt.Errorf("need six public input combination points, found %d", count)
	}
	vk.G1.K = make([]curve.G1Affine, 6)
	for i := range vk.G1.K {
		if err := dec.Decode(&vk.G1.K[i]); err != nil {
			return nil, digest, err
		}
	}
	for _, section := range []string{"public commitments", "commitment keys"} {
		if err := binary.Read(r, binary.BigEndian, &count); err != nil {
			return nil, digest, err
		}
		if count != 0 {
			return nil, digest, fmt.Errorf("unsupported %s section", section)
		}
	}
	if r.Len() != 0 {
		return nil, digest, fmt.Errorf("trailing verification key bytes")
	}
	if err := vk.Precompute(); err != nil {
		return nil, digest, err
	}
	return &vk, digest, nil
}

func versionForKey(id [32]byte) string {
	switch hex.EncodeToString(id[:]) {
	case "4388a21c687fdd5f218d7e3d13190cac4c5355818d3605fd5fb811df468ee696":
		return "v6.1.0"
	case "0e78f4db7a6771a3a6a7d9c3b0de6fe73d58781368967a7fe84d87aefffec896":
		return "v6.0.0"
	default:
		return "gnark-bn254-5-input"
	}
}

func canonicalDecimal(s string, modulus *big.Int) (*big.Int, error) {
	if len(s) == 0 || len(s) > 78 || (len(s) > 1 && s[0] == '0') {
		return nil, fmt.Errorf("expected canonical decimal field element")
	}
	for _, c := range s {
		if c < '0' || c > '9' {
			return nil, fmt.Errorf("expected canonical decimal field element")
		}
	}
	v, ok := new(big.Int).SetString(s, 10)
	if !ok || v.Cmp(modulus) >= 0 {
		return nil, fmt.Errorf("field element outside modulus")
	}
	return v, nil
}

func inputScalars(data []byte) (fr.Vector, error) {
	var values []string
	if err := json.Unmarshal(data, &values); err != nil {
		return nil, err
	}
	if len(values) != 5 {
		return nil, fmt.Errorf("expected five canonical scalar inputs")
	}
	inputs := make(fr.Vector, 5)
	for i, s := range values {
		v, err := canonicalDecimal(s, fr.Modulus())
		if err != nil {
			return nil, fmt.Errorf("input %d: %w", i, err)
		}
		inputs[i].SetBigInt(v)
	}
	return inputs, nil
}

// Go's ordinary object unmarshal silently accepts duplicate properties and
// case-insensitive field names. A decoded proof has one exact field per axis.
func object(data []byte, names ...string) (map[string]json.RawMessage, error) {
	dec := json.NewDecoder(bytes.NewReader(data))
	start, err := dec.Token()
	if err != nil || start != json.Delim('{') {
		return nil, fmt.Errorf("expected proof object")
	}
	fields := make(map[string]json.RawMessage, len(names))
	for dec.More() {
		nameToken, err := dec.Token()
		if err != nil {
			return nil, err
		}
		name, ok := nameToken.(string)
		if !ok {
			return nil, fmt.Errorf("expected property name")
		}
		if !slices.Contains(names, name) || fields[name] != nil {
			return nil, fmt.Errorf("unexpected or duplicate property %q", name)
		}
		var value json.RawMessage
		if err := dec.Decode(&value); err != nil {
			return nil, err
		}
		fields[name] = value
	}
	if _, err := dec.Token(); err != nil {
		return nil, err
	}
	if _, err := dec.Token(); err != io.EOF {
		return nil, fmt.Errorf("trailing proof object data")
	}
	if len(fields) != len(names) {
		return nil, fmt.Errorf("missing proof object property")
	}
	return fields, nil
}

func coordinate(s string) (fp.Element, error) {
	v, err := canonicalDecimal(s, fp.Modulus())
	var out fp.Element
	if err == nil {
		out.SetBigInt(v)
	}
	return out, err
}

func decodeG1(data []byte) (curve.G1Affine, error) {
	var p curve.G1Affine
	f, err := object(data, "x", "y")
	if err != nil {
		return p, err
	}
	for _, axis := range []struct {
		name string
		dest *fp.Element
	}{{"x", &p.X}, {"y", &p.Y}} {
		var s string
		if err := json.Unmarshal(f[axis.name], &s); err != nil {
			return p, err
		}
		*axis.dest, err = coordinate(s)
		if err != nil {
			return p, err
		}
	}
	if !p.IsInSubGroup() {
		return p, fmt.Errorf("invalid G1 point")
	}
	return p, nil
}

func decodeG2(data []byte) (curve.G2Affine, error) {
	var p curve.G2Affine
	f, err := object(data, "x", "y")
	if err != nil {
		return p, err
	}
	for _, axis := range []struct {
		name string
		dest *curve.E2
	}{{"x", &p.X}, {"y", &p.Y}} {
		var values []string
		if err := json.Unmarshal(f[axis.name], &values); err != nil {
			return p, err
		}
		if len(values) != 2 {
			return p, fmt.Errorf("each twist coordinate requires two base-field elements")
		}
		axis.dest.A0, err = coordinate(values[0])
		if err != nil {
			return p, err
		}
		axis.dest.A1, err = coordinate(values[1])
		if err != nil {
			return p, err
		}
	}
	if !p.IsInSubGroup() {
		return p, fmt.Errorf("invalid G2 subgroup point")
	}
	return p, nil
}

func verifyDecoded(key *native.VerifyingKey, inputs fr.Vector, data []byte) error {
	f, err := object(data, "a", "b", "c")
	if err != nil {
		return err
	}
	var p native.Proof
	if p.Ar, err = decodeG1(f["a"]); err != nil {
		return fmt.Errorf("a: %w", err)
	}
	if p.Bs, err = decodeG2(f["b"]); err != nil {
		return fmt.Errorf("b: %w", err)
	}
	if p.Krs, err = decodeG1(f["c"]); err != nil {
		return fmt.Errorf("c: %w", err)
	}
	return native.Verify(&p, key, inputs)
}

func specialize(version string, key *native.VerifyingKey, id [32]byte, inputs fr.Vector) (fixedStatement, curve.G1Affine, error) {
	l, err := statementPoint(key, inputs)
	if err != nil {
		return fixedStatement{}, l, err
	}
	inputStrings := make([]string, len(inputs))
	for i := range inputs {
		inputStrings[i] = inputs[i].Text(10)
	}
	return fixedStatement{
		Version: version, KeyDigest: hex.EncodeToString(id[:]), Inputs: inputStrings,
		L: g1(l), Gamma: g2(key.G2.Gamma), Alpha: g1(key.G1.Alpha),
		Beta: g2(key.G2.Beta), Delta: g2(key.G2.Delta),
	}, l, nil
}

func runStatement(mode, keyPath, inputsPath string, stdin io.Reader, stdout io.Writer) error {
	raw, err := limitedFile(keyPath, keyLimit)
	if err != nil {
		return err
	}
	key, id, err := parseKey(raw)
	if err != nil {
		return err
	}
	data, err := limitedFile(inputsPath, jsonLimit)
	if err != nil {
		return err
	}
	inputs, err := inputScalars(data)
	if err != nil {
		return err
	}
	if mode == "-verify-decoded" {
		proof, err := limitedBytes(stdin, jsonLimit)
		if err != nil {
			return err
		}
		if err := verifyDecoded(key, inputs, proof); err != nil {
			return err
		}
		_, err = fmt.Fprintln(stdout, "verified")
		return err
	}
	stmt, _, err := specialize(versionForKey(id), key, id, inputs)
	if err != nil {
		return err
	}
	enc := json.NewEncoder(stdout)
	enc.SetIndent("", "  ")
	return enc.Encode(stmt)
}
