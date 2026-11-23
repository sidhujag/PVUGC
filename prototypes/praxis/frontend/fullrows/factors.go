package fullrows

import (
	"errors"
	"math/big"
	"math/bits"
	"sort"

	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
)

type domainCache map[int]*fft.Domain
type kernel struct {
	values   []fr.Element
	spectrum []fr.Element
	domain   *fft.Domain
}

func centered(a, m *big.Int) *big.Int {
	half := new(big.Int).Rsh(new(big.Int).Set(m), 1)
	x := new(big.Int).Add(a, half)
	x.Mod(x, m)
	return x.Sub(x, half)
}

func newKernel(c *big.Int, n, w, t int, domains domainCache) *kernel {
	k := &kernel{values: make([]fr.Element, n)}
	if w == 0 {
		k.values[0].SetBigInt(c)
		return k
	}
	p := fp.Modulus()
	a := centered(c, p)
	low := new(big.Int).Lsh(big.NewInt(1), uint(t))
	for i := range k.values {
		if t != 0 {
			k.values[i].SetBigInt(centered(a, low))
		} else {
			k.values[i].SetBigInt(a)
		}
		if i+1 < n {
			a = centered(a.Lsh(a, uint(w)), p)
		}
	}
	if n >= 64 {
		size := 1 << bits.Len(uint(n-1))
		d := domains[size]
		if d == nil {
			d = fft.NewDomain(uint64(size))
			domains[size] = d
		}
		k.domain = d
		k.spectrum = make([]fr.Element, size)
		copy(k.spectrum, k.values)
		d.FFT(k.spectrum, fft.DIF, fft.WithNbTasks(1))
	}
	return k
}

// slide computes sum_i in[i]*C[i+j] at each output j. The circular
// convolution may wrap only into positions below len(in)-1, which are unused.
func (k *kernel) slide(in, out, scratch []fr.Element) {
	if len(in)*len(out) < 2048 || k.domain == nil {
		for j := range out {
			var v, acc fr.Element
			for i := range in {
				v.Mul(&k.values[i+j], &in[i])
				acc.Add(&acc, &v)
			}
			out[j] = acc
		}
		return
	}
	sc := scratch[:len(k.spectrum)]
	clear(sc)
	for i, v := range in {
		sc[len(in)-1-i] = v
	}
	k.domain.FFT(sc, fft.DIF, fft.WithNbTasks(1))
	for i := range sc {
		sc[i].Mul(&sc[i], &k.spectrum[i])
	}
	k.domain.FFTInverse(sc, fft.DIT, fft.WithNbTasks(1))
	copy(out, sc[len(in)-1:])
}

func (a atom) read(w []byte) fr.Element {
	if a == oneAtom {
		return fr.One()
	}
	// Extract chunks of at most 8 bits, most significant first. This also
	// handles the 254-bit direct slice without allocating a big.Int.
	if a.width <= 8 {
		j := a.start / 8
		x := uint16(w[j])
		if a.start%8+a.width > 8 {
			x |= uint16(w[j+1]) << 8
		}
		return fr.NewElement(uint64((x >> uint(a.start%8)) & ((1 << uint(a.width)) - 1)))
	}
	var v fr.Element
	for rem := a.width; rem > 0; {
		n := min(rem, 8)
		chunk := atom{a.start + rem - n, n}.read(w)
		for i := 0; i < n; i++ {
			v.Double(&v)
		}
		v.Add(&v, &chunk)
		rem -= n
	}
	return v
}
func (a atom) scatter(v fr.Element, target []fr.Element) {
	if a == oneAtom {
		target[0].Add(&target[0], &v)
		return
	}
	start := a.start + 1
	for i := 0; i < a.width; i++ {
		target[start+i].Add(&target[start+i], &v)
		v.Double(&v)
	}
}

// A term may have the same original left wire as many other terms. Cache its
// indices in the sorted factors of this row for this evaluation only.
type digitSpan struct {
	a    atom
	w, t int
}
type factorIndex map[digitSpan][]int

func (m factorIndex) span(left []atom, a atom, w, t int) []int {
	key := digitSpan{a, w, t}
	if list, ok := m[key]; ok {
		return list
	}
	result := make([]int, a.count(w))
	for i := range result {
		want := a.digit(i, w, t)
		k := sort.Search(len(left), func(j int) bool { return !less(left[j], want) })
		// The keys and operations are built by the same authenticated parser.
		result[i] = k
	}
	m[key] = result
	return result
}

// AddWeighted adds the two weighted columns used by a QAP at its secret setup
// evaluation point. The left and right weighting vectors may differ. The
// transpose of the public sliding convolution yields the right bit coefficients
// in batches, without writing the dense BQS matrix.
func (r Row) AddWeighted(a, b, leftWeights, rightWeights []fr.Element) error {
	if len(a) != r.unknowns+1 || len(b) != r.unknowns+1 || len(leftWeights) != r.Count() || len(rightWeights) != r.Count() {
		return errors.New("bad affine column dimensions")
	}
	for i, atom := range r.left {
		atom.scatter(leftWeights[i], a)
	}
	index := factorIndex{}
	var in, out [254]fr.Element
	var scratch [512]fr.Element
	for _, op := range r.ops {
		list := index.span(r.left, op.x, op.width, op.clip)
		for i, pos := range list {
			in[i] = rightWeights[pos]
		}
		n := op.y.count(op.width)
		op.k.slide(in[:len(list)], out[:n], scratch[:])
		for j := 0; j < n; j++ {
			v := out[j]
			if !op.scale.IsOne() {
				v.Mul(&v, &op.scale)
			}
			op.y.digit(j, op.width, op.clip).scatter(v, b)
		}
	}
	return nil
}

// Evaluate returns the values of the individual affine factors, in exactly
// the order used by AddWeighted and the standalone Python frontend.
func (r Row) Evaluate(w []byte) (left, right []fr.Element, err error) {
	if err = checkBits(r.unknowns, w); err != nil {
		return nil, nil, err
	}
	left = make([]fr.Element, r.Count())
	right = make([]fr.Element, r.Count())
	for i, a := range r.left {
		left[i] = a.read(w)
	}
	index := factorIndex{}
	var in, out [254]fr.Element
	var scratch [512]fr.Element
	for _, op := range r.ops {
		list := index.span(r.left, op.x, op.width, op.clip)
		n := op.y.count(op.width)
		for j := 0; j < n; j++ {
			in[j] = op.y.digit(j, op.width, op.clip).read(w)
		}
		op.k.slide(in[:n], out[:len(list)], scratch[:])
		for i, pos := range list {
			v := out[i]
			if !op.scale.IsOne() {
				v.Mul(&v, &op.scale)
			}
			right[pos].Add(&right[pos], &v)
		}
	}
	return left, right, nil
}
