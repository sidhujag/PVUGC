// Package fullqap constructs the scalar-field QAP in Praxis Definition 4.6.
// The number of variables, constraints, and public polynomial degrees are exact.
// FFT scratch points outside the interpolation set never become variables or rows.
package fullqap

import (
	"errors"
	"math/big"
	"math/bits"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
)

type binomial struct {
	shift int // exponent k = 2^shift in X^k - c
	c     fr.Element
}

type Domain struct {
	N, Rows, Nu, D, CosetSize   int
	roots                       []fr.Element // powers of an ambient generator, in bit-reversed order
	ambient                     *fft.Domain
	p0, points, holes, rowHoles []binomial
}

func New(variables, rows, nu int) (*Domain, error) {
	// BN254 Fr has 2-adicity 28. The convolution needs at most 2*|H| points.
	const limit = 1 << 27
	if variables < 1 || variables > limit-2 || rows < 1 || nu < 2 || nu&(nu-1) != 0 || rows > (limit-2-variables)/nu {
		return nil, errors.New("unsupported QAP shape or convolution domain")
	}
	m := rows * nu
	size := variables + 2 + m
	h := nextPower(size)
	ambient := fft.NewDomain(uint64(h), fft.WithoutPrecompute())
	roots := make([]fr.Element, h)
	fft.BuildExpTable(ambient.Generator, roots)
	fft.BitReverse(roots)
	d := &Domain{N: variables, Rows: rows, Nu: nu, D: size, CosetSize: m, roots: roots, ambient: ambient}
	d.p0 = d.factors(m, size)
	d.points = d.factors(0, size)
	d.holes = d.factors(size, h)
	d.rowHoles = d.factors(m, nextPower(m))
	return d, nil
}

func nextPower(n int) int { return 1 << bits.Len(uint(n-1)) }

// Aligned blocks of 2^j consecutive bit-reversed indices form cosets of the
// order-2^j subgroup. All their members obey x^(2^j) = roots[start >> j].
func (d *Domain) factors(start, end int) []binomial {
	var out []binomial
	for start < end {
		shift := min(bits.TrailingZeros(uint(start)), bits.Len(uint(end-start))-1)
		out = append(out, binomial{shift, d.roots[start>>shift]})
		start += 1 << shift
	}
	return out
}

func (d *Domain) atIndex(factors []binomial, i int) fr.Element {
	product := fr.One()
	var term fr.Element
	for _, f := range factors {
		term.Sub(&d.roots[i>>f.shift], &f.c)
		product.Mul(&product, &term)
	}
	return product
}

func evaluateFactors(factors []binomial, x fr.Element) fr.Element {
	product := fr.One()
	var term fr.Element
	for _, f := range factors {
		term.Exp(x, big.NewInt(int64(1)<<f.shift))
		term.Sub(&term, &f.c)
		product.Mul(&product, &term)
	}
	return product
}

// reciprocalDerivative uses (X^|H|-1)'(rho) = |H|/rho and the product
// of the unused-point factors to return 1/fullZ'(rho).
func (d *Domain) reciprocalDerivative() fr.Element {
	i := d.D - 1
	c := d.atIndex(d.holes, i)
	c.Mul(&c, &d.roots[i]).Mul(&c, &d.ambient.CardinalityInv)
	return c
}

// divideBinomials computes the quotient by a product of monic binomials.
// A low-degree remainder discarded at each step cannot affect the final
// quotient. Interpolation calls also verify that every division is exact.
func divideBinomials(coeff []fr.Element, factors []binomial, exact bool) ([]fr.Element, error) {
	var term fr.Element
	for _, f := range factors {
		k := 1 << f.shift
		if k > len(coeff) {
			return nil, errors.New("binomial exceeds polynomial length")
		}
		for i := len(coeff) - 1; i >= k; i-- {
			term.Mul(&coeff[i], &f.c)
			coeff[i-k].Add(&coeff[i-k], &term)
		}
		if exact {
			for i := range k {
				if !coeff[i].IsZero() {
					return nil, errors.New("nonzero interpolation division remainder")
				}
			}
		}
		coeff = coeff[k:]
	}
	return coeff, nil
}

// interpolate recovers the unique polynomial on a prefix of bit-reversed
// points. The ambient IFFT gives f(X)*C(X), where C vanishes on the unused
// suffix. Dividing out C yields the exact-degree interpolation.
func (d *Domain) interpolate(values []fr.Element, count int, holes []binomial, grid *fft.Domain) error {
	for i := 0; i < count; i++ {
		c := d.atIndex(holes, i)
		values[i].Mul(&values[i], &c)
	}
	grid.FFTInverse(values, fft.DIT)
	coeff, err := divideBinomials(values, holes, true)
	if err != nil {
		return err
	}
	copy(values, coeff)
	clear(values[count:])
	return nil
}
