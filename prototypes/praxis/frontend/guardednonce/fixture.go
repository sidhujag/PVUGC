// Package guardednonce exercises the honest Bitcoin signing equations of a
// two-stage guarded affine nonce. A centralized fixture holds every secret.
// Its two caller-supplied authorization functions model ideal selective release.
// This package does not implement a public capsule, Syscoin verifier, or MPC.
package guardednonce

import (
	"crypto/rand"
	"errors"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/btcec/v2/schnorr"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
)

type scalar = btcec.ModNScalar
type point = btcec.JacobianPoint

// Setup contains full signed compressed points except the BIP340 x-only key.
// Context is a fixed-width commitment to the application, reserve and input role.
type Setup struct {
	Context, Key [32]byte
	H            [33]byte
	C, T         [3][33]byte
}

type Opening struct {
	B, Z [32]byte
}

type Nonce struct {
	X   [32]byte
	Odd bool // parity of U before lifting the BIP340 nonce to even Y
}

// Policy is a substitute for an authenticated source proof in the fixture.
// Every deployment needs fresh signing material and a policy pinned to its role.
type Policy func(context, digest [32]byte) bool

type Dealer struct {
	setup                     Setup
	x                         scalar
	k, b, rho                 [3]scalar
	firstAllowed, nextAllowed Policy
}

// SampleH samples a uniform nonidentity point by rejecting invalid compressed
// encodings, without computing its discrete logarithm relative to G. A real
// system must define how every participant agrees upon the CRS.
func SampleH() ([33]byte, error) {
	for {
		var h [33]byte
		if _, err := rand.Read(h[:]); err != nil {
			return [33]byte{}, err
		}
		h[0] = 2 + h[0]%2
		if _, err := btcec.ParsePubKey(h[:]); err == nil {
			return h, nil
		}
	}
}

func randomScalar() (scalar, error) {
	var raw [32]byte
	defer clear(raw[:])
	for {
		if _, err := rand.Read(raw[:]); err != nil {
			return scalar{}, err
		}
		var x scalar
		if x.SetBytes(&raw) == 0 {
			return x, nil
		}
	}
}

func parsePoint(encoded [33]byte) (point, error) {
	key, err := btcec.ParsePubKey(encoded[:])
	if err != nil {
		return point{}, err
	}
	var p point
	key.AsJacobian(&p)
	return p, nil
}

func encode(p point) ([33]byte, bool) {
	if p.Z.IsZero() {
		return [33]byte{}, false
	}
	p.ToAffine()
	return [33]byte(btcec.NewPublicKey(&p.X, &p.Y).SerializeCompressed()), true
}

func baseMul(s *scalar) (p point) {
	btcec.ScalarBaseMultNonConst(s, &p)
	return p
}

func mul(s *scalar, p point) (r point) {
	btcec.ScalarMultNonConst(s, &p, &r)
	return r
}

func add(p, q point) (r point) {
	btcec.AddNonConst(&p, &q, &r)
	return r
}

// NewDealer creates an honest demonstration setup. The stage authorizers
// independently decide which specific digests each ideal release will serve.
// A two-view experiment supplies at most two distinct authorized digests total.
func NewDealer(context [32]byte, h [33]byte, firstAllowed, nextAllowed Policy) (*Dealer, error) {
	if firstAllowed == nil || nextAllowed == nil {
		return nil, errors.New("missing stage authorization policy")
	}
	hp, err := parsePoint(h)
	if err != nil {
		return nil, err
	}
	dealer := &Dealer{setup: Setup{Context: context, H: h}, firstAllowed: firstAllowed, nextAllowed: nextAllowed}
	var xp point
	for {
		dealer.x, err = randomScalar()
		if err != nil {
			return nil, err
		}
		if dealer.x.IsZero() {
			continue
		}
		public, _ := encode(baseMul(&dealer.x))
		if public[0] == 3 {
			dealer.x.Negate()
		}
		copy(dealer.setup.Key[:], public[1:])
		xp = baseMul(&dealer.x)
		break
	}
	for j := range 3 {
		for {
			for _, value := range []*scalar{&dealer.k[j], &dealer.b[j], &dealer.rho[j]} {
				*value, err = randomScalar()
				if err != nil {
					return nil, err
				}
			}
			c, validC := encode(add(baseMul(&dealer.k[j]), mul(&dealer.b[j], xp)))
			t, validT := encode(add(mul(&dealer.b[j], hp), baseMul(&dealer.rho[j])))
			if validC && validT {
				dealer.setup.C[j], dealer.setup.T[j] = c, t
				break
			}
		}
	}
	return dealer, nil
}

func (d *Dealer) Public() Setup { return d.setup }

// Each big-endian 128-bit half fits in the scalar field. In a fixed setup,
// distinct 32-byte digests give distinct rows (1, left, right).
func digestHalves(digest [32]byte) [2]scalar {
	var halves [2]scalar
	halves[0].SetByteSlice(digest[:16])
	halves[1].SetByteSlice(digest[16:])
	return halves
}

func evaluate(coefficients *[3]scalar, halves *[2]scalar) scalar {
	v := coefficients[0]
	for j := range halves {
		var term scalar
		term.Mul2(&coefficients[j+1], &halves[j])
		v.Add(&term)
	}
	return v
}

func evaluatePoints(coefficients [3][33]byte, halves *[2]scalar) (point, error) {
	p, err := parsePoint(coefficients[0])
	if err != nil {
		return point{}, err
	}
	for j := range halves {
		term, err := parsePoint(coefficients[j+1])
		if err != nil {
			return point{}, err
		}
		p = add(p, mul(&halves[j], term))
	}
	return p, nil
}

func (d *Dealer) First(digest [32]byte) (Opening, error) {
	if !d.firstAllowed(d.setup.Context, digest) {
		return Opening{}, errors.New("first-stage policy did not authorize this digest")
	}
	halves := digestHalves(digest)
	b, z := evaluate(&d.b, &halves), evaluate(&d.rho, &halves)
	return Opening{B: b.Bytes(), Z: z.Bytes()}, nil
}

// Nonce checks BH+ZG=T(digest), computes U=C(digest)-BX, and rejects infinity.
func (s Setup) Nonce(digest [32]byte, open Opening) (Nonce, error) {
	var b, z scalar
	if b.SetBytes(&open.B) != 0 || z.SetBytes(&open.Z) != 0 {
		return Nonce{}, errors.New("noncanonical opening scalar")
	}
	halves := digestHalves(digest)
	h, err := parsePoint(s.H)
	if err != nil {
		return Nonce{}, err
	}
	t, err := evaluatePoints(s.T, &halves)
	if err != nil {
		return Nonce{}, err
	}
	want, wantFinite := encode(t)
	got, gotFinite := encode(add(mul(&b, h), baseMul(&z)))
	if wantFinite != gotFinite || want != got {
		return Nonce{}, errors.New("guard commitment disagrees with opening")
	}
	c, err := evaluatePoints(s.C, &halves)
	if err != nil {
		return Nonce{}, err
	}
	x, err := schnorr.ParsePubKey(s.Key[:])
	if err != nil {
		return Nonce{}, err
	}
	var xp point
	x.AsJacobian(&xp)
	b.Negate()
	p, finite := encode(add(c, mul(&b, xp)))
	if !finite {
		return Nonce{}, errors.New("identity signing nonce")
	}
	return Nonce{X: [32]byte(p[1:]), Odd: p[0] == 3}, nil
}

// Second releases one native signature only under the fixture's separate
// second-stage policy. A valid guard opening alone is not an authorization.
func (d *Dealer) Second(digest [32]byte, open Opening) ([64]byte, error) {
	if !d.nextAllowed(d.setup.Context, digest) {
		return [64]byte{}, errors.New("second-stage policy did not authorize this digest")
	}
	nonce, err := d.setup.Nonce(digest, open)
	if err != nil {
		return [64]byte{}, err
	}
	halves := digestHalves(digest)
	k := evaluate(&d.k, &halves)
	if nonce.Odd {
		k.Negate()
	}
	hash := chainhash.TaggedHash(chainhash.TagBIP0340Challenge, nonce.X[:], d.setup.Key[:], digest[:])
	var e, response scalar
	e.SetBytes((*[32]byte)(hash)) // BIP340 requires reduction modulo the group order.
	response.Mul2(&e, &d.x).Add(&k)
	s := response.Bytes()
	var signature [64]byte
	copy(signature[:32], nonce.X[:])
	copy(signature[32:], s[:])
	return signature, nil
}
