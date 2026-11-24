package fullkem

import (
	"bytes"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// A witness with exactly one selected wire gives the same public polynomial
// identity and tests both additive points and the powers of tau. The compact
// frontend's integration tests supply the independently constructed real QAP.
func TestCapsuleTwoWitnesses(t *testing.T) {
	s := Shape{N: 3, D: 9, Nu: 2, CosetSize: 4, Statement: [32]byte{11}}
	fullWitness := []bool{true, false, false}
	otherWitness := []bool{false, false, true}
	rho := fromInt(5)
	roots := func(tau scalar) (scalar, scalar) {
		z0, z := one, one
		for i := 0; i < s.D; i++ {
			node := fromInt(i + 1)
			if i <= s.N+1 {
				z0 = mul(z0, sub(tau, node))
			}
			if node != rho {
				z = mul(z, sub(tau, node))
			}
		}
		return z0, z
	}
	_, normal := roots(rho)
	cornerCoeff := inv(normal)
	q := []scalar{fromInt(3), fromInt(2)}
	// Zfull / Z = X-rho, hence otherQ=(X-rho)*keyQ+cornerCoeff.
	o := Openings{KeyQ: q, OtherQ: []scalar{add(neg(mul(rho, q[0])), cornerCoeff), sub(q[0], mul(rho, q[1])), q[1]}, Remainder: []scalar{{}, fromInt(4), {}, fromInt(7)}}
	eval := func(tau fr.Element) (Evaluations, error) {
		z0, z := roots(tau)
		full := mul(z, sub(tau, rho))
		corner := mul(z, cornerCoeff)
		h := add(q[0], mul(tau, q[1]))
		r := mul(tau, add(o.Remainder[1], mul(mul(tau, tau), o.Remainder[3])))
		p := add(corner, add(mul(full, h), mul(z0, r)))
		return Evaluations{A: []scalar{{}, p, p, p}, B: []scalar{one, {}, {}, {}}, FullZ: full, Z: z, Z0: z0, Corner: corner}, nil
	}
	var out bytes.Buffer
	want, err := Encrypt(&out, s, eval)
	if err != nil {
		t.Fatal(err)
	}
	wire := out.Bytes()
	size, err := WireBytes(s)
	if err != nil || int64(len(wire)) != size {
		t.Fatalf("wire size %d != %d (%v)", len(wire), size, err)
	}
	for _, w := range [][]bool{fullWitness, otherWitness} {
		got, err := Decrypt(bytes.NewReader(wire), s, w, o)
		if err != nil || got != want {
			t.Fatalf("witness %v: %v, equality %v", w, err, got == want)
		}
	}
	if _, err := Decrypt(bytes.NewReader(wire), s, []bool{true, true, false}, o); err == nil {
		t.Fatal("accepted incorrect opening")
	}
	wrong := s
	wrong.Statement[1]++
	if _, err := Decrypt(bytes.NewReader(wire), wrong, otherWitness, o); err == nil {
		t.Fatal("accepted mismatched digest")
	}
	bad := append([]byte{}, wire...)
	bad[len(bad)-1] |= 1
	if _, err := Decrypt(bytes.NewReader(bad), s, otherWitness, o); err == nil {
		t.Fatal("accepted masked seed padding")
	}
	bad = append([]byte{}, wire...)
	for j := 120; j < 152; j++ {
		bad[j] = 0xff
	}
	if _, err := Decrypt(bytes.NewReader(bad), s, otherWitness, o); err == nil {
		t.Fatal("accepted malformed point")
	}
}
func TestFixedBases(t *testing.T) {
	s := make([]scalar, 193)
	s[3] = one
	for i := 4; i < len(s); i++ {
		if _, err := s[i].SetRandom(); err != nil {
			t.Fatal(err)
		}
	}
	p1, p2 := fixedG1(s), fixedG2(s)
	r1 := bn254.BatchScalarMultiplicationG1(&g1Base, s)
	r2 := bn254.BatchScalarMultiplicationG2(&g2Base, s)
	for i := range s {
		if !p1[i].Equal(&r1[i]) || !p2[i].Equal(&r2[i]) {
			t.Fatalf("fixed-generator table mismatch at %d", i)
		}
	}
}
func TestBoundedSearch(t *testing.T) {
	const ones = 356481
	for _, n := range []int{2 * ones, 3*ones + 355, 9 * ones} {
		v, err := findSearchExponent(gtBase, gtInt(gtBase, n), ones, false)
		if err != nil || v != n {
			t.Fatalf("search %d returned %d (%v)", n, v, err)
		}
	}
	if _, err := findSearchExponent(gtBase, gtInt(gtBase, 9*ones+1), ones, false); err == nil {
		t.Fatal("accepted outside range")
	}
	var id bn254.GT
	id.SetOne()
	if v, err := findSearchExponent(id, id, ones, false); err != nil || v != 2*ones {
		t.Fatalf("identity search %d %v", v, err)
	}
	if _, err := findSearchExponent(id, id, ones, true); err == nil {
		t.Fatal("unique-coordinate search accepted an ambiguous exponent")
	}
}

// Exercise the separately encoded constant column, the first and second
// coefficient of a matrix column, and the final partial block.
func TestRecoveryAcrossBlocks(t *testing.T) {
	const n = blockWidth + 3
	s := Shape{N: n, D: n + 4, Nu: 2, CosetSize: 2}
	w := make([]bool, n)
	w[0], w[1], w[blockWidth+2] = true, true, true
	// The polynomial identity P=1, keyQ=0 and otherQ=1 has constant
	// corner and Z equal to 1. This backend fixture isolates the group sums.
	eval := func(fr.Element) (Evaluations, error) {
		e := Evaluations{A: make([]scalar, n+1), B: make([]scalar, n+1), FullZ: one, Z: one, Z0: one, Corner: one}
		e.B[0] = one
		e.A[1] = fromInt(9)
		e.A[2] = neg(fromInt(5))
		e.A[n] = neg(fromInt(3))
		return e, nil
	}
	var b bytes.Buffer
	want, err := Encrypt(&b, s, eval)
	if err != nil {
		t.Fatal(err)
	}
	size, err := WireBytes(s)
	if err != nil || int64(b.Len()) != size {
		t.Fatalf("size %d, %d, %v", b.Len(), size, err)
	}
	got, err := Decrypt(&b, s, w, Openings{OtherQ: []scalar{one}})
	if err != nil || got != want {
		t.Fatalf("block recovery %v, equality %v", err, got == want)
	}
}
