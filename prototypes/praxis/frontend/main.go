// Measure a BN254-on-BN254 Groth16 verifier for a fixed SP1 statement.
package main

import (
	"bytes"
	"crypto/sha256"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"runtime"
	"strings"

	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	native "github.com/consensys/gnark/backend/groth16/bn254"
	"github.com/consensys/gnark/constraint"
	csbn "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/logger"
	"github.com/consensys/gnark/std/algebra/emulated/sw_bn254"
	"github.com/consensys/gnark/std/math/emulated"
	rec "github.com/consensys/gnark/std/recursion/groth16"
)

//go:embed testdata/*
var files embed.FS

type proofVar = rec.Proof[sw_bn254.G1Affine, sw_bn254.G2Affine]
type vkVar = rec.VerifyingKey[sw_bn254.G1Affine, sw_bn254.G2Affine, sw_bn254.GTEl]
type witnessVar = rec.Witness[sw_bn254.ScalarField]
type circuit struct {
	Proof  proofVar
	Key    vkVar      `gnark:"-"`
	Inputs witnessVar `gnark:"-"`
}

func (c *circuit) Define(api frontend.API) error {
	v, err := rec.NewVerifier[sw_bn254.ScalarField, sw_bn254.G1Affine, sw_bn254.G2Affine, sw_bn254.GTEl](api)
	if err != nil {
		return err
	}
	// gnark v0.16 uses complete scalar arithmetic by default.
	return v.AssertProof(c.Key, c.Proof, c.Inputs, rec.WithSubgroupCheck())
}

func readKey(version string) (*native.VerifyingKey, [32]byte, error) {
	data, err := files.ReadFile("testdata/sp1-" + version + ".vk")
	if err != nil {
		return nil, [32]byte{}, err
	}
	return parseKey(data)
}

func readFixture(version string, keyID [32]byte) (*native.Proof, fr.Vector, error) {
	data, err := files.ReadFile("testdata/sp1-" + version + ".json")
	if err != nil {
		return nil, nil, err
	}
	var f struct{ Vkey, PublicValues, Proof string }
	if err := json.Unmarshal(data, &f); err != nil {
		return nil, nil, err
	}
	program, err := hex.DecodeString(strings.TrimPrefix(f.Vkey, "0x"))
	if err != nil || len(program) != 32 {
		return nil, nil, fmt.Errorf("invalid program key")
	}
	public, err := hex.DecodeString(strings.TrimPrefix(f.PublicValues, "0x"))
	if err != nil {
		return nil, nil, err
	}
	blob, err := hex.DecodeString(strings.TrimPrefix(f.Proof, "0x"))
	if err != nil || len(blob) != 4+3*32+256 || !bytes.Equal(blob[:4], keyID[:4]) {
		return nil, nil, fmt.Errorf("proof selector, size, or encoding differs from verification key")
	}
	hash := sha256.Sum256(public)
	hash[0] &= 0x1f
	inputs := make(fr.Vector, 5)
	for i, value := range [][]byte{program, hash[:], blob[4:36], blob[36:68], blob[68:100]} {
		if err := inputs[i].SetBytesCanonical(value); err != nil {
			return nil, nil, err
		}
	}
	if !inputs[2].IsZero() {
		return nil, nil, fmt.Errorf("unexpected nonzero SP1 exit code")
	}
	var p native.Proof
	d := curve.NewDecoder(bytes.NewReader(blob[100:]))
	for _, point := range []any{&p.Ar, &p.Bs, &p.Krs} {
		if err := d.Decode(point); err != nil {
			return nil, nil, err
		}
	}
	if d.BytesRead() != 256 {
		return nil, nil, fmt.Errorf("unexpected proof point length")
	}
	return &p, inputs, nil
}

func compile(key *native.VerifyingKey, input fr.Vector) (constraint.ConstraintSystem, error) {
	vk, err := rec.ValueOfVerifyingKeyFixed[sw_bn254.G1Affine, sw_bn254.G2Affine, sw_bn254.GTEl](key)
	if err != nil {
		return nil, err
	}
	var values witnessVar
	for i := range input {
		values.Public = append(values.Public, emulated.ValueOf[sw_bn254.ScalarField](input[i]))
	}
	return frontend.Compile(fr.Modulus(), r1cs.NewBuilder, &circuit{Key: vk, Inputs: values})
}

func measure(version string, ccs constraint.ConstraintSystem) error {
	internal, secret, public := ccs.GetNbInternalVariables(), ccs.GetNbSecretVariables(), ccs.GetNbPublicVariables()
	if public != 1 {
		return fmt.Errorf("key or inputs became witness variables")
	}
	bits := int64(fr.Modulus().BitLen()) * int64(internal+secret)
	fmt.Printf("%s: rows=%d internal_wires=%d private_inputs=%d public_wires_including_one=%d commitment_slots=%d boolean_unknowns=%d left_factor_bytes_at_K1_192=%d\n",
		version, ccs.GetNbConstraints(), internal, secret, public, len(ccs.GetCommitments().CommitmentIndexes()), bits, 2*32*192*(bits+1))
	return nil
}

// gnark normally replaces this hint with the outer proving system's commitment.
// The diagnostic solver can evaluate a valid witness without a second CRS by
// deriving a nonzero challenge from all of the hint's inputs. The raw R1CS
// does not constrain this transcript hash.
func diagnosticChallenge(mod *big.Int, inputs, outputs []*big.Int) error {
	h := sha256.New()
	h.Write([]byte("PVUGC/gnark/diagnostic-challenge/v1"))
	var word [32]byte
	for _, input := range inputs {
		h.Write(input.FillBytes(word[:]))
	}
	outputs[0].SetBytes(h.Sum(nil)).Mod(outputs[0], mod)
	if outputs[0].Sign() == 0 {
		outputs[0].SetInt64(1)
	}
	return nil
}
func solve(ccs constraint.ConstraintSystem, proof *native.Proof) error {
	p, err := rec.ValueOfProof[sw_bn254.G1Affine, sw_bn254.G2Affine](proof)
	if err != nil {
		return err
	}
	w, err := frontend.NewWitness(&circuit{Proof: p}, fr.Modulus())
	if err != nil {
		return err
	}
	result, err := ccs.Solve(w, solver.OverrideHint(solver.GetHintID(cs.Bsb22CommitmentComputePlaceholder), diagnosticChallenge))
	if err != nil {
		return err
	}
	return checkBooleanTrace(ccs.(*csbn.R1CS), result.(*csbn.R1CSSolution))
}

// Encode every nonconstant wire in 254 Boolean digits, substitute the
// resulting binary linear forms for the field wires and evaluate each row.
// Recombining the 254 digits in a single field operation below avoids
// materializing an enormous list of repeated polynomial coefficients.
func checkBooleanTrace(ccs *csbn.R1CS, solution *csbn.R1CSSolution) error {
	values := make(fr.Vector, len(solution.W))
	values[0].SetOne()
	if !values[0].Equal(&solution.W[0]) {
		return fmt.Errorf("unexpected constant wire")
	}
	for i := 1; i < len(values); i++ {
		bits := solution.W[i].Bytes()
		if bits[0]&0xc0 != 0 {
			return fmt.Errorf("wire %d outside 254 bits", i)
		}
		if err := values[i].SetBytesCanonical(bits[:]); err != nil {
			return err
		}
	}
	eval := func(line constraint.LinearExpression) fr.Element {
		var sum, term fr.Element
		for _, t := range line {
			c := &ccs.Coefficients[t.CoeffID()]
			if t.IsConstant() {
				sum.Add(&sum, c)
				continue
			}
			term.Mul(c, &values[t.WireID()])
			sum.Add(&sum, &term)
		}
		return sum
	}
	it := ccs.GetR1CIterator()
	count := 0
	for row := it.Next(); row != nil; row = it.Next() {
		l, r, o := eval(row.L), eval(row.R), eval(row.O)
		if !l.Mul(&l, &r).Equal(&o) {
			return fmt.Errorf("binary substituted row %d failed", count)
		}
		count++
	}
	if count != ccs.GetNbConstraints() {
		return fmt.Errorf("evaluated %d of %d constraint rows", count, ccs.GetNbConstraints())
	}
	return nil
}

func checkFixture(version string) (fr.Vector, error) {
	key, id, err := readKey(version)
	if err != nil {
		return nil, err
	}
	proof, inputs, err := readFixture(version, id)
	if err != nil {
		return nil, err
	}
	second, err := rescaled(proof)
	if err != nil {
		return nil, err
	}
	ccs, err := compile(key, inputs)
	if err != nil {
		return nil, err
	}
	if err = measure(version, ccs); err != nil {
		return nil, err
	}
	for i, p := range []*native.Proof{proof, second} {
		if err := native.Verify(p, key, inputs); err != nil {
			return nil, fmt.Errorf("native proof %d: %w", i, err)
		}
		if err := solve(ccs, p); err != nil {
			return nil, fmt.Errorf("circuit proof %d: %w", i, err)
		}
	}
	ccs = nil
	runtime.GC()
	wrong := append(fr.Vector(nil), inputs...)
	one := fr.One()
	wrong[1].Add(&wrong[1], &one)
	if err := native.Verify(proof, key, wrong); err == nil {
		return nil, fmt.Errorf("native verifier accepted changed public input")
	}
	bad, err := compile(key, wrong)
	if err != nil {
		return nil, err
	}
	if err := solve(bad, proof); err == nil {
		return nil, fmt.Errorf("circuit accepted changed public input")
	}
	fmt.Printf("%s: both distinct proofs accepted; different public-values hash rejected by both native verifier and diagnostic solver\n", version)
	return inputs, nil
}

func run() error {
	if len(os.Args) > 1 {
		if len(os.Args) == 2 && os.Args[1] == "-export-v6.1" {
			logger.Disable()
			return exportPairings(os.Stdout, "v6.1.0")
		}
		if len(os.Args) == 4 && (os.Args[1] == "-statement" || os.Args[1] == "-verify-decoded") {
			logger.Disable()
			return runStatement(os.Args[1], os.Args[2], os.Args[3], os.Stdin, os.Stdout)
		}
		return fmt.Errorf("usage: frontend [-export-v6.1 | -statement RAW_VK INPUTS_JSON | -verify-decoded RAW_VK INPUTS_JSON]")
	}
	_, err := checkFixture("v6.0.0")
	if err != nil {
		return err
	}
	runtime.GC()
	_, id, err := readKey("v6.1.0")
	if err != nil {
		return err
	}
	if _, _, err := readFixture("v6.0.0", id); err == nil {
		return fmt.Errorf("version-mismatched selector accepted")
	}
	_, err = checkFixture("v6.1.0")
	return err
}
func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
