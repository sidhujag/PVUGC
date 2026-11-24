package fullkem

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
)

type accum struct {
	forms poly4
	left  [3]bn254.G1Jac
	right [2][legs][2]bn254.G2Jac
}

func (a *accum) readColumns(r io.Reader, start, n int, w []bool) error {
	matrix := make([][2]scalar, matrixCount(start, n))
	for j := range matrix {
		for k := range matrix[j] {
			var b [32]byte
			if _, err := io.ReadFull(r, b[:]); err != nil {
				return err
			}
			if err := matrix[j][k].SetBytesCanonical(b[:]); err != nil {
				return err
			}
		}
	}
	p, err := readG1(r, 3*n)
	if err != nil {
		return err
	}
	q, err := readG2(r, 24*n)
	if err != nil {
		return err
	}
	for i := range n {
		if start+i != 0 && !w[start+i-1] {
			continue
		}
		z := column(start, i, matrix)
		for j, v := range z {
			a.forms[j] = add(a.forms[j], v)
		}
		for j := range 3 {
			a.left[j].AddMixed(&p[3*i+j])
		}
		for k := range 2 {
			for leg := range legs {
				for j := range 2 {
					a.right[k][leg][j].AddMixed(&q[24*i+k*12+leg*2+j])
				}
			}
		}
	}
	return nil
}
func coeff(p []scalar, i int) scalar {
	if i >= len(p) {
		return scalar{}
	}
	return p[i]
}
func readPowerSums(r io.Reader, count, skip int, polys ...[]scalar) ([]bn254.G1Affine, error) {
	sums := make([]bn254.G1Jac, len(polys))
	indices := make([]int, 0, pointChunk)
	process := func() error {
		points, err := readG1(r, len(indices))
		if err != nil {
			return err
		}
		scalars := make([]scalar, len(indices))
		for j, p := range polys {
			for i, idx := range indices {
				scalars[i] = coeff(p, idx)
			}
			var sum bn254.G1Jac
			if _, err := sum.MultiExp(points, scalars, ecc.MultiExpConfig{}); err != nil {
				return err
			}
			sums[j].AddAssign(&sum)
		}
		indices = indices[:0]
		return nil
	}
	for i := range count {
		if skip != 0 && i%skip == 0 {
			continue
		}
		indices = append(indices, i)
		if len(indices) == cap(indices) {
			if err := process(); err != nil {
				return nil, err
			}
		}
	}
	if len(indices) > 0 {
		if err := process(); err != nil {
			return nil, err
		}
	}
	out := make([]bn254.G1Affine, len(sums))
	for i := range sums {
		out[i].FromJacobian(&sums[i])
	}
	return out, nil
}
func g2MSM(p []bn254.G2Affine, s []scalar) (v bn254.G2Affine, err error) {
	_, err = v.MultiExp(p, s, ecc.MultiExpConfig{})
	return
}
func combine(a *accum, cp int, extras []bn254.G2Affine, t cancellation, keyQ, othQ, rem bn254.G1Affine) (bn254.GT, bn254.GT, error) {
	var none bn254.GT
	f := make([]bn254.G1Affine, 3)
	for i := range f {
		f[i].FromJacobian(&a.left[i])
	}
	left := make([]bn254.G1Affine, 0, 2*legs+4)
	right := make([]bn254.G2Affine, 0, 2*legs+4)
	searchLeft := make([]bn254.G1Affine, legs)
	for leg, w := range t.weights {
		weight := asBig(w)
		for j := range 2 {
			var p bn254.G1Affine
			p.ScalarMultiplication(&f[j], weight)
			left = append(left, p)
			var q bn254.G2Affine
			q.FromJacobian(&a.right[cp][leg][j])
			right = append(right, q)
			if j == 0 {
				searchLeft[leg] = p
			}
		}
	}
	var keyBase bn254.G2Affine
	keyBase.ScalarMultiplication(&extras[6], asBig(t.weights[0]))
	othBase, err := g2MSM(extras[7:12], t.weights[1:])
	if err != nil {
		return none, none, err
	}
	remBase, err := g2MSM(extras[12:18], t.weights[:])
	if err != nil {
		return none, none, err
	}
	tieCo := make([]scalar, 0, 44)
	for _, row := range t.tie {
		tieCo = append(tieCo, row[:]...)
	}
	for _, row := range t.plus {
		tieCo = append(tieCo, row[:]...)
	}
	for _, row := range t.minus {
		tieCo = append(tieCo, row[:]...)
	}
	tieBase, err := g2MSM(extras[18:], tieCo)
	if err != nil {
		return none, none, err
	}
	for _, p := range []bn254.G1Affine{keyQ, othQ, rem, f[2]} {
		var negative bn254.G1Affine
		negative.Neg(&p)
		left = append(left, negative)
	}
	right = append(right, keyBase, othBase, remBase, tieBase)
	lambda, err := bn254.Pair(left, right)
	if err != nil {
		return none, none, err
	}
	psi, err := bn254.Pair(searchLeft, extras[:6])
	return lambda, psi, err
}

// Decrypt opens a complete canonical group capsule using the caller's local
// Boolean witness and the corresponding QAP openings. Regardless of bit value,
// every serialized source point undergoes decoding and subgroup validation.
func Decrypt(src io.Reader, s Shape, witness []bool, o Openings) ([32]byte, error) {
	return decode(src, s, witness, o, nil)
}

// SearchSum reads an ordinary development table and returns the unique bounded
// search integer for these witness and QAP openings. For an honest valid
// assignment it equals r_constant + sum_i r_i*w_i. The caller obtains the
// openings from its authenticated QAP. It rejects an ambiguous search even
// when the ordinary fixed-message decoder can still recover its payload.
func SearchSum(src io.Reader, s Shape, witness []bool, o Openings) (int, error) {
	var sum int
	_, err := decode(src, s, witness, o, &sum)
	return sum, err
}

func decode(src io.Reader, s Shape, witness []bool, o Openings, searchSum *int) ([32]byte, error) {
	var none [32]byte
	if err := s.validate(); err != nil {
		return none, err
	}
	if len(witness) != s.N {
		return none, errors.New("incorrect Boolean witness length")
	}
	if err := validateOpenings(s, o); err != nil {
		return none, err
	}
	r := bufio.NewReaderSize(src, 1<<20)
	if err := checkHeader(r, s); err != nil {
		return none, err
	}
	var a accum
	if err := blocks(s.N, func(start, n int) error {
		if err := a.readColumns(r, start, n, witness); err != nil {
			return fmt.Errorf("invalid variable block at %d: %w", start, err)
		}
		return nil
	}); err != nil {
		return none, err
	}
	t, err := makeTies(a.forms)
	if err != nil {
		return none, err
	}
	qs, err := readPowerSums(r, s.D, 0, o.KeyQ, o.OtherQ)
	if err != nil {
		return none, err
	}
	rs, err := readPowerSums(r, s.CosetSize, s.Nu, o.Remainder)
	if err != nil {
		return none, err
	}
	extras, err := readG2(r, 2*extraCount)
	if err != nil {
		return none, err
	}
	var b [384]byte
	if _, err := io.ReadFull(r, b[:]); err != nil {
		return none, err
	}
	var alphaKey bn254.GT
	if err := alphaKey.SetBytes(b[:]); err != nil {
		return none, err
	}
	if alphaKey.IsZero() || alphaKey.IsOne() || !alphaKey.IsInSubGroup() {
		return none, errors.New("invalid alpha-key subgroup element")
	}
	canonical := alphaKey.Bytes()
	if !bytes.Equal(canonical[:], b[:]) {
		return none, errors.New("noncanonical alpha key")
	}
	var masked [13]byte
	if _, err := io.ReadFull(r, masked[:]); err != nil {
		return none, err
	}
	if masked[12]&15 != 0 {
		return none, errors.New("invalid masked seed padding")
	}
	if err := eoi(r); err != nil {
		return none, err
	}
	alphaLambda, alphaPsi, err := combine(&a, 1, extras[extraCount:], t, qs[0], qs[1], rs[0])
	if err != nil {
		return none, err
	}
	target := gtExp(alphaKey, t.weights[0])
	target.InverseUnitary(&target)
	target.Mul(&target, &alphaLambda)
	ones := 1
	for _, set := range witness {
		if set {
			ones++
		}
	}
	rw, err := findSearchExponent(alphaPsi, target, ones, searchSum != nil)
	if err != nil {
		return none, err
	}
	if searchSum != nil {
		*searchSum = rw
		return none, nil
	}
	lambda, psi, err := combine(&a, 0, extras[:extraCount], t, qs[0], qs[1], rs[0])
	if err != nil {
		return none, err
	}
	key := gtInt(psi, rw)
	key.InverseUnitary(&key)
	key.Mul(&key, &lambda)
	key = gtExp(key, inv(t.weights[0]))
	seed := seedMask(key, s.Statement, masked)
	defer clear(seed[:])
	return expandSeed(seed, s.Statement), nil
}
