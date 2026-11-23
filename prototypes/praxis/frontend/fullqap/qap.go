package fullqap

import (
	"errors"
	"fmt"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"pvugc.example/praxis-frontend/fullrows"
)

// ErrDomainPoint requests a new tau when sampling hits a QAP node.
var ErrDomainPoint = errors.New("QAP sampling point lies in evaluation set")

type Setup struct {
	A, B                 []fr.Element
	Z0, Z, FullZ, Corner fr.Element
}

type Opening struct {
	KeyQ, OtherQ, Remainder []fr.Element
}

func (d *Domain) checkSystem(s *fullrows.System) error {
	if s == nil || d.N != s.Unknowns || d.Rows != len(s.Rows) {
		return errors.New("system does not match QAP shape")
	}
	for i, row := range s.Rows {
		if row.Count() >= d.Nu {
			return fmt.Errorf("row %d has no spare RHS slot", i)
		}
	}
	return nil
}

// lagrange returns the full-set Lagrange weights at tau for consecutive slots.
// For p in the set, 1/fullZ'(p) = p*C(p)/|H|. Batch inversions keep the number
// of field inversions independent of the number of points within the batch.
func (d *Domain) lagrange(tau, normalizedZ fr.Element, start, count int) []fr.Element {
	den := make([]fr.Element, count)
	for i := range den {
		den[i].Sub(&tau, &d.roots[start+i])
	}
	out := fr.BatchInvert(den)
	for i := range out {
		index := start + i
		c := d.atIndex(d.holes, index)
		out[i].Mul(&out[i], &normalizedZ).Mul(&out[i], &d.roots[index]).Mul(&out[i], &c)
	}
	return out
}

// Setup returns the public QAP polynomials evaluated at the given secret
// point. The first wire is the constant 1. For each sum-to-zero BQS row the
// reserved RHS slot has A = Z0*e0 and B = 0, as required by Definition 4.6.
func (d *Domain) Setup(tau fr.Element, s *fullrows.System) (*Setup, error) {
	if err := d.checkSystem(s); err != nil {
		return nil, err
	}
	out := &Setup{A: make([]fr.Element, d.N+1), B: make([]fr.Element, d.N+1)}
	out.FullZ = evaluateFactors(d.points, tau)
	if out.FullZ.IsZero() {
		return nil, ErrDomainPoint
	}
	out.Z0 = evaluateFactors(d.p0, tau)
	var tauMinusRho, normalizedZ fr.Element
	tauMinusRho.Sub(&tau, &d.roots[d.D-1])
	out.Z.Div(&out.FullZ, &tauMinusRho)
	cornerScale := d.reciprocalDerivative()
	out.Corner.Mul(&out.Z, &cornerScale)
	normalizedZ.Mul(&out.FullZ, &d.ambient.CardinalityInv)
	out.A[0] = out.Corner
	out.B[0] = out.Corner
	for start := 0; start <= d.N; start += 4096 {
		weights := d.lagrange(tau, normalizedZ, d.CosetSize+start, min(4096, d.N+1-start))
		for off, weight := range weights {
			i := start + off
			if i == 0 {
				out.B[0].Add(&out.B[0], &weight)
				continue
			}
			out.A[i], out.B[i] = weight, weight
			out.A[0].Sub(&out.A[0], &weight)
		}
	}
	for i, row := range s.Rows {
		start := i * d.Nu
		right := d.lagrange(tau, normalizedZ, start, d.Nu)
		left := make([]fr.Element, row.Count())
		for slot := range left {
			z0 := d.atIndex(d.p0, start+slot)
			left[slot].Mul(&right[slot], &z0)
		}
		last := d.Nu - 1
		z0 := d.atIndex(d.p0, start+last)
		z0.Mul(&z0, &right[last])
		out.A[0].Add(&out.A[0], &z0)
		if err := row.AddWeighted(out.A, out.B, left, right[:row.Count()]); err != nil {
			return nil, err
		}
	}
	return out, nil
}

// Open computes Equation (4) using only public rows and packed little-endian
// witness bits. KeyQ and OtherQ have D-1 and D coefficients respectively.
// Remainder has nu*rows coefficients, including zero at forbidden exponents.
func (d *Domain) Open(witness []byte, s *fullrows.System) (*Opening, error) {
	if err := d.checkSystem(s); err != nil {
		return nil, err
	}
	if len(witness) != (d.N+7)/8 || d.N%8 != 0 && witness[len(witness)-1]>>uint(d.N%8) != 0 {
		return nil, errors.New("invalid witness length or nonzero padding bits")
	}
	h := len(d.roots)
	rowGridSize := nextPower(d.CosetSize)
	a, b := make([]fr.Element, 2*h), make([]fr.Element, 2*h)
	r := make([]fr.Element, rowGridSize)
	for i, row := range s.Rows {
		left, right, err := row.Evaluate(witness)
		if err != nil {
			return nil, err
		}
		var sum fr.Element
		for j := range left {
			at := i*d.Nu + j
			z0 := d.atIndex(d.p0, at)
			a[at].Mul(&z0, &left[j])
			b[at] = right[j]
			r[at].Mul(&left[j], &right[j])
			sum.Add(&sum, &r[at])
		}
		if !sum.IsZero() {
			return nil, fmt.Errorf("unsatisfied BQS row %d", i)
		}
		last := (i+1)*d.Nu - 1
		a[last] = d.atIndex(d.p0, last)
	}
	minusOne := fr.One()
	minusOne.Neg(&minusOne)
	b[d.CosetSize].SetOne()
	for i := range d.N {
		slot := d.CosetSize + 1 + i
		if witness[i>>3]>>(i&7)&1 != 0 {
			b[slot].SetOne()
		} else {
			a[slot] = minusOne
		}
	}
	a[d.D-1].SetOne()
	b[d.D-1].SetOne()

	rowGrid := fft.NewDomain(uint64(rowGridSize), fft.WithoutPrecompute())
	if err := d.interpolate(r, d.CosetSize, d.rowHoles, rowGrid); err != nil {
		return nil, err
	}
	for i := 0; i < d.CosetSize; i += d.Nu {
		if !r[i].IsZero() {
			return nil, fmt.Errorf("forbidden remainder exponent %d", i)
		}
	}
	if err := d.interpolate(a[:h], d.D, d.holes, d.ambient); err != nil {
		return nil, err
	}
	if err := d.interpolate(b[:h], d.D, d.holes, d.ambient); err != nil {
		return nil, err
	}
	mulGrid := fft.NewDomain(uint64(2*h), fft.WithoutPrecompute())
	mulGrid.FFT(a, fft.DIF)
	mulGrid.FFT(b, fft.DIF)
	for i := range a {
		a[i].Mul(&a[i], &b[i])
	}
	mulGrid.FFTInverse(a, fft.DIT)
	// Z0*R + Lrho has degree <D. Hence the quotient of A*B by fullZ is
	// precisely h_key. Also Lrho=Z/fullZ'(rho), so the second quotient is
	// (X-rho)*h_key + 1/fullZ'(rho). Neither division needs secret data.
	q, err := divideBinomials(a[:2*d.D-1], d.points, false)
	if err != nil {
		return nil, err
	}
	key := append([]fr.Element(nil), q...)
	other := make([]fr.Element, d.D)
	copy(other[1:], key)
	rho := d.roots[d.D-1]
	for i := range key {
		var term fr.Element
		term.Mul(&key[i], &rho)
		other[i].Sub(&other[i], &term)
	}
	cornerScale := d.reciprocalDerivative()
	other[0].Add(&other[0], &cornerScale)
	return &Opening{KeyQ: key, OtherQ: other, Remainder: r[:d.CosetSize:d.CosetSize]}, nil
}
