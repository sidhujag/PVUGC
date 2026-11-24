package fullkem

import (
	"bufio"
	"crypto/rand"
	"errors"
	"io"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// ErrDomainPoint may be returned by evaluate when tau hits an interpolation node.
var ErrDomainPoint = errors.New("QAP evaluation point in public interpolation domain")

type coins struct {
	tau, omega12, omega22, alpha, pi, upsilon, epsilon scalar
	sKind, zeta, eta                                   [3]scalar
}

func drawNonzero(x *scalar) error {
	for {
		if _, err := x.SetRandom(); err != nil {
			return err
		}
		if !x.IsZero() {
			return nil
		}
	}
}
func drawCoins() (c coins, err error) {
	if _, err = c.omega12.SetRandom(); err != nil {
		return
	}
	for _, x := range []*scalar{&c.omega22, &c.alpha, &c.pi, &c.upsilon, &c.sKind[0], &c.sKind[1], &c.sKind[2], &c.zeta[0], &c.zeta[1], &c.zeta[2], &c.eta[0], &c.eta[1], &c.eta[2]} {
		if err = drawNonzero(x); err != nil {
			return
		}
	}
	for {
		if err = drawNonzero(&c.epsilon); err != nil {
			return
		}
		if c.epsilon != neg(one) {
			break
		}
	}
	return
}

type factorScales struct {
	piLeft, invOmega22, negArg, midArg, posArg scalar
	s, gamma, weightPower, shiftedPower        [legs]scalar
}

func makeScales(c coins) (f factorScales) {
	f.piLeft = mul(c.pi, add(one, c.epsilon))
	f.invOmega22 = inv(c.omega22)
	f.negArg = neg(mul(c.upsilon, inv(omega)))
	f.midArg = neg(c.upsilon)
	f.posArg = neg(mul(omega, c.upsilon))
	var pw, ps [4]scalar
	pw[0] = one
	ps[0] = one
	for j := 1; j < 4; j++ {
		pw[j] = mul(pw[j-1], c.upsilon)
		ps[j] = mul(ps[j-1], f.posArg)
	}
	for leg, e := range legExp {
		f.weightPower[leg] = pw[e]
		f.shiftedPower[leg] = mul(ps[e], inv(c.epsilon))
		f.s[leg] = mul(c.sKind[legKind[leg]], pw[e])
		f.gamma[leg] = mul(f.piLeft, f.s[leg])
	}
	return
}
func matrixCount(start, n int) int {
	if start == 0 {
		return 1
	}
	return (n + 1) / 2
}
func column(start, i int, m [][2]scalar) (z [4]scalar) {
	if start == 0 {
		z[0] = one
		z[2] = m[0][0]
		z[3] = m[0][1]
		return
	}
	p := m[i/2]
	if i%2 == 0 {
		z[2] = p[0]
		z[3] = p[1]
	} else {
		z[2] = neg(p[1])
		z[3] = p[0]
	}
	return
}
func eval(z [4]scalar, x scalar) scalar {
	return add(z[0], mul(x, add(z[1], mul(x, add(z[2], mul(x, z[3]))))))
}

// scratchCapture holds only the requested wire positions, excluding the constant
// column. This is private setup state and is never serialized with the table.
type scratchCapture struct {
	positions map[int]int
	values    []byte
}

func writeColumns(w io.Writer, start, n int, e Evaluations, c coins, f factorScales, scratch *scratchCapture) error {
	matrix := make([][2]scalar, matrixCount(start, n))
	for i := range matrix {
		for j := range matrix[i] {
			if _, err := matrix[i][j].SetRandom(); err != nil {
				return err
			}
			data := matrix[i][j].Bytes()
			if _, err := w.Write(data[:]); err != nil {
				return err
			}
		}
	}
	// Each small r entry uses three independent bits, hence is exactly uniform on 2..9.
	small := make([]byte, n)
	if _, err := io.ReadFull(rand.Reader, small); err != nil {
		return err
	}
	left := make([]scalar, 3*n)
	right := make([]scalar, 24*n)
	defer clear(left)
	defer clear(right)
	defer clear(small)
	for i := range n {
		var y scalar
		if _, err := y.SetRandom(); err != nil {
			return err
		}
		a, b := e.A[start+i], e.B[start+i]
		value := 2 + (small[i] & 7)
		if scratch != nil {
			if pos, ok := scratch.positions[start+i-1]; ok {
				scratch.values[pos] = value
			}
		}
		r := fromInt(int(value))
		left[3*i] = mul(f.piLeft, y)
		left[3*i+1] = mul(f.piLeft, add(mul(c.omega12, y), mul(c.omega22, a)))
		left[3*i+2] = mul(c.zeta[2], y)
		z := column(start, i, matrix)
		zm, zc, zp := eval(z, f.negArg), eval(z, f.midArg), eval(z, f.posArg)
		t1 := add(mul(c.eta[0], zc), mul(c.eta[1], zp))
		t2 := add(mul(c.eta[1], zm), mul(c.eta[2], zc))
		t3 := sub(mul(c.eta[2], zp), mul(c.eta[0], zm))
		for leg := range legs {
			theta := mul(f.weightPower[leg], t3)
			if legKind[leg] != 2 {
				theta = sub(mul(f.weightPower[leg], t1), mul(f.shiftedPower[leg], t2))
			}
			second := mul(mul(f.s[leg], sub(b, y)), f.invOmega22)
			first := sub(add(mul(f.s[leg], add(r, a)), theta), mul(c.omega12, second))
			at := i*24 + leg*2
			right[at], right[at+1] = first, second
			right[at+12], right[at+13] = mul(c.alpha, first), mul(c.alpha, second)
		}
	}
	if err := writeG1(w, left); err != nil {
		return err
	}
	return writeG2(w, right)
}

func writePowers(w io.Writer, count, skip int, tau, zeta scalar) error {
	buf := make([]scalar, 0, pointChunk)
	defer clear(buf[:cap(buf)])
	p := zeta
	for i := range count {
		if skip == 0 || i%skip != 0 {
			buf = append(buf, p)
			if len(buf) == cap(buf) {
				if err := writeG1(w, buf); err != nil {
					return err
				}
				buf = buf[:0]
			}
		}
		p = mul(p, tau)
	}
	if len(buf) > 0 {
		return writeG1(w, buf)
	}
	return nil
}
func extraScalars(c coins, f factorScales, e Evaluations) []scalar {
	v := make([]scalar, 0, 2*extraCount)
	v = append(v, f.s[:]...)
	iz := inv(c.zeta[0])
	ir := inv(c.zeta[1])
	iy := inv(c.zeta[2])
	for leg := range legs {
		z := e.Z
		if leg == 0 {
			z = e.FullZ
		}
		v = append(v, mul(f.gamma[leg], mul(z, iz)))
	}
	for leg := range legs {
		v = append(v, mul(f.gamma[leg], mul(e.Z0, ir)))
	}
	u2 := mul(c.upsilon, c.upsilon)
	pu := sub(mul(u2, u2), c0)
	appendPowers := func(a int, scale scalar, n int) {
		p := mul(mul(mul(c.pi, c.eta[a]), iy), scale)
		for range n {
			v = append(v, p)
			p = mul(p, c.upsilon)
		}
	}
	for a := range 3 {
		appendPowers(a, pu, 3)
	}
	for a := range 3 {
		appendPowers(a, c.epsilon, 7)
	}
	for a := 1; a < 3; a++ {
		appendPowers(a, inv(c.epsilon), 7)
	}
	for i := range extraCount {
		v = append(v, mul(c.alpha, v[i]))
	}
	return v
}

// Encrypt writes a capsule and returns the independently sampled DEM key. Only
// the public relation enters evaluate. Its argument and results are secret
// ephemeral encryption material, never part of the capsule.
func Encrypt(dst io.Writer, s Shape, evaluate func(fr.Element) (Evaluations, error)) ([32]byte, error) {
	return encrypt(dst, s, evaluate, nil)
}

// EncryptWithScratch writes one ordinary development table and returns the
// sampled coefficients of the designated Boolean wires to the setup caller.
// The entries range from 2 to 9. They are suitable for correctness fixtures
// only. An index is zero-based in the witness, without the constant column.
func EncryptWithScratch(dst io.Writer, s Shape, evaluate func(fr.Element) (Evaluations, error), wireIndices []int) ([]byte, error) {
	scratch := scratchCapture{positions: make(map[int]int, len(wireIndices)), values: make([]byte, len(wireIndices))}
	for pos, wire := range wireIndices {
		if wire < 0 || wire >= s.N {
			return nil, errors.New("scratch wire out of range")
		}
		if _, exists := scratch.positions[wire]; exists {
			return nil, errors.New("duplicate scratch wire")
		}
		scratch.positions[wire] = pos
	}
	key, err := encrypt(dst, s, evaluate, &scratch)
	clear(key[:])
	if err != nil {
		clear(scratch.values)
		return nil, err
	}
	return scratch.values, nil
}

func encrypt(dst io.Writer, s Shape, evaluate func(fr.Element) (Evaluations, error), scratch *scratchCapture) ([32]byte, error) {
	var none [32]byte
	if err := s.validate(); err != nil {
		return none, err
	}
	if evaluate == nil {
		return none, errors.New("missing public QAP evaluator")
	}
	c, err := drawCoins()
	if err != nil {
		return none, err
	}
	var e Evaluations
	for {
		if _, err = c.tau.SetRandom(); err != nil {
			return none, err
		}
		e, err = evaluate(c.tau)
		if errors.Is(err, ErrDomainPoint) {
			continue
		}
		if err != nil {
			return none, err
		}
		if !e.FullZ.IsZero() {
			break
		}
	}
	if len(e.A) != s.N+1 || len(e.B) != s.N+1 || e.Corner.IsZero() || e.Z0.IsZero() || e.Z.IsZero() {
		return none, errors.New("inconsistent public QAP evaluation")
	}
	f := makeScales(c)
	out := bufio.NewWriterSize(dst, 1<<20)
	if _, err = out.Write(s.header()); err != nil {
		return none, err
	}
	if err = blocks(s.N, func(start, n int) error { return writeColumns(out, start, n, e, c, f, scratch) }); err != nil {
		return none, err
	}
	if err = writePowers(out, s.D, 0, c.tau, c.zeta[0]); err != nil {
		return none, err
	}
	if err = writePowers(out, s.CosetSize, s.Nu, c.tau, c.zeta[1]); err != nil {
		return none, err
	}
	extras := extraScalars(c, f, e)
	defer clear(extras)
	if err = writeG2(out, extras); err != nil {
		return none, err
	}
	keyGT := gtExp(gtBase, mul(f.gamma[0], e.Corner))
	alphaGT := gtExp(keyGT, c.alpha)
	b := alphaGT.Bytes()
	if _, err = out.Write(b[:]); err != nil {
		return none, err
	}
	var seed [13]byte
	defer clear(seed[:])
	if _, err = io.ReadFull(rand.Reader, seed[:]); err != nil {
		return none, err
	}
	seed[12] &= 0xf0
	masked := seedMask(keyGT, s.Statement, seed)
	if _, err = out.Write(masked[:]); err != nil {
		return none, err
	}
	if err = out.Flush(); err != nil {
		return none, err
	}
	return expandSeed(seed, s.Statement), nil
}
