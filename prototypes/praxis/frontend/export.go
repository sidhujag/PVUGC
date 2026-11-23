// Export the fixed statement separately from two variable Groth16 witnesses.
package main

import (
	"encoding/json"
	"fmt"
	"io"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	native "github.com/consensys/gnark/backend/groth16/bn254"
)

type g1JSON struct {
	X string `json:"x"`
	Y string `json:"y"`
}

type g2JSON struct {
	X [2]string `json:"x"`
	Y [2]string `json:"y"`
}

func g1(p curve.G1Affine) g1JSON {
	return g1JSON{p.X.Text(10), p.Y.Text(10)}
}

func g2(p curve.G2Affine) g2JSON {
	return g2JSON{[2]string{p.X.A0.Text(10), p.X.A1.Text(10)}, [2]string{p.Y.A0.Text(10), p.Y.A1.Text(10)}}
}

type fixedStatement struct {
	Version   string   `json:"version"`
	KeyDigest string   `json:"vk_sha256"`
	Inputs    []string `json:"public_inputs"`
	L         g1JSON   `json:"L"`
	Gamma     g2JSON   `json:"gamma"`
	Alpha     g1JSON   `json:"alpha"`
	Beta      g2JSON   `json:"beta"`
	Delta     g2JSON   `json:"delta"`
}

type proofJSON struct {
	A g1JSON `json:"a"`
	B g2JSON `json:"b"`
	C g1JSON `json:"c"`
}

type pairingFixture struct {
	Statement fixedStatement `json:"statement"`
	Witnesses []proofJSON    `json:"witnesses"`
}

func rescaled(proof *native.Proof) (*native.Proof, error) {
	other := *proof
	two := big.NewInt(2)
	other.Ar.ScalarMultiplication(&proof.Ar, two)
	other.Bs.ScalarMultiplication(&proof.Bs, new(big.Int).ModInverse(two, fr.Modulus()))
	if other.Ar.Equal(&proof.Ar) || other.Bs.Equal(&proof.Bs) {
		return nil, fmt.Errorf("rescaling did not change both proof components")
	}
	return &other, nil
}

func statementPoint(key *native.VerifyingKey, inputs fr.Vector) (curve.G1Affine, error) {
	var l curve.G1Affine
	if len(key.G1.K) != len(inputs)+1 {
		return l, fmt.Errorf("wrong number of public inputs")
	}
	if _, err := l.MultiExp(key.G1.K[1:], inputs, ecc.MultiExpConfig{}); err != nil {
		return l, err
	}
	l.Add(&l, &key.G1.K[0])
	return l, nil
}

// The exporter checks the four-pair product independently of the BQS lowering.
func productCheck(key *native.VerifyingKey, l curve.G1Affine, proof *native.Proof) (bool, error) {
	var cNeg, lNeg, aNeg curve.G1Affine
	cNeg.Neg(&proof.Krs)
	lNeg.Neg(&l)
	aNeg.Neg(&key.G1.Alpha)
	return curve.PairingCheck([]curve.G1Affine{proof.Ar, cNeg, lNeg, aNeg}, []curve.G2Affine{proof.Bs, key.G2.Delta, key.G2.Gamma, key.G2.Beta})
}

func exportPairings(out io.Writer, version string) error {
	key, id, err := readKey(version)
	if err != nil {
		return err
	}
	proof, inputs, err := readFixture(version, id)
	if err != nil {
		return err
	}
	other, err := rescaled(proof)
	if err != nil {
		return err
	}
	stmt, l, err := specialize(version, key, id, inputs)
	if err != nil {
		return err
	}
	fixture := pairingFixture{Statement: stmt}
	for _, p := range []*native.Proof{proof, other} {
		if err := native.Verify(p, key, inputs); err != nil {
			return err
		}
		ok, err := productCheck(key, l, p)
		if err != nil {
			return err
		}
		if !ok {
			return fmt.Errorf("fixed pairing product failed")
		}
		fixture.Witnesses = append(fixture.Witnesses, proofJSON{g1(p.Ar), g2(p.Bs), g1(p.Krs)})
	}

	wrong := append(fr.Vector(nil), inputs...)
	one := fr.One()
	wrong[1].Add(&wrong[1], &one)
	wrongL, err := statementPoint(key, wrong)
	if err != nil {
		return err
	}
	ok, err := productCheck(key, wrongL, proof)
	if err != nil {
		return err
	}
	if ok || native.Verify(proof, key, wrong) == nil {
		return fmt.Errorf("wrong public-values digest accepted")
	}

	e := json.NewEncoder(out)
	e.SetIndent("", "  ")
	return e.Encode(fixture)
}
