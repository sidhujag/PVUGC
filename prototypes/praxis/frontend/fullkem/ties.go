package fullkem

import (
	"errors"
	"math"

	"github.com/consensys/gnark-crypto/ecc/bn254"
)

// With four forms, the products before reduction have at most seven
// monomials. The quotient by T^4-c0 therefore has at most three.
type poly4 = [4]scalar
type poly7 = [7]scalar

func product(a, b poly4) (c poly7) {
	for i, x := range a {
		for j, y := range b {
			c[i+j] = add(c[i+j], mul(x, y))
		}
	}
	return
}
func substitute(p poly4, s scalar) (q poly4) {
	u := one
	for i, x := range p {
		q[i] = mul(x, u)
		u = mul(u, s)
	}
	return
}
func difference(a, b poly7) (q poly7) {
	for i := range q {
		q[i] = sub(a[i], b[i])
	}
	return
}
func reduce(p poly7) (q poly4) {
	copy(q[:], p[:4])
	for i := 0; i < 3; i++ {
		q[i] = add(q[i], mul(c0, p[4+i]))
	}
	return
}

type cancellation struct {
	weights [legs]scalar
	tie     [3][3]scalar
	plus    [3]poly7
	minus   [2]poly7
}

func makeTies(z poly4) (t cancellation, err error) {
	negZ := substitute(z, neg(inv(omega)))
	mid := substitute(z, neg(one))
	pos := substitute(z, neg(omega))
	u := reduce(product(z, negZ))
	v := reduce(product(z, mid))
	us := substitute(u, neg(omega))
	for leg, e := range legExp {
		if legKind[leg] == 2 {
			t.weights[leg] = v[e]
		} else {
			t.weights[leg] = u[e]
		}
	}
	if t.weights[0].IsZero() {
		return t, errors.New("zero key weight for this witness")
	}
	t.plus[0] = difference(product(u, mid), product(v, negZ))
	t.plus[1] = product(u, pos)
	t.plus[2] = product(v, pos)
	t.minus[0] = difference(poly7{}, product(us, negZ))
	t.minus[1] = difference(poly7{}, product(us, mid))
	for i := range 3 {
		p := t.plus[i]
		if i > 0 {
			for j := range p {
				p[j] = add(p[j], t.minus[i-1][j])
			}
		}
		remainder := reduce(p)
		if remainder != (poly4{}) {
			return t, errors.New("extension-field cancellation polynomial has a remainder")
		}
		copy(t.tie[i][:], p[4:])
	}
	return t, nil
}

// The g=8 honest search interval contains 7*ones+1 candidate exponents.
// Baby-step/giant-step is exact. A full canonical GT string is the map key.
func findSearchExponent(base, target bn254.GT, ones int, requireUnique bool) (int, error) {
	// Every representable interval here is far shorter than the BN254 prime
	// subgroup order, so its integer representative is unique for a nonidentity base.
	if ones < 1 || ones > math.MaxInt/(g+1) {
		return 0, errors.New("invalid bounded search interval")
	}
	lower, span := 2*ones, (g-1)*ones
	if base.IsOne() {
		if requireUnique {
			return 0, errors.New("identity search base has no unique exponent")
		}
		if target.IsOne() {
			return lower, nil
		}
		return 0, errors.New("nonidentity search target with identity base")
	}
	first := gtInt(base, lower)
	first.InverseUnitary(&first)
	var goal bn254.GT
	goal.Mul(&target, &first)
	step := int(math.Sqrt(float64(span+1))) + 1
	babies := make(map[[384]byte]int, step)
	var u bn254.GT
	u.SetOne()
	for j := range step {
		babies[u.Bytes()] = j
		u.Mul(&u, &base)
	}
	u.InverseUnitary(&u)
	for offset := 0; offset <= span; offset += step {
		if j, ok := babies[goal.Bytes()]; ok && offset+j <= span {
			return lower + offset + j, nil
		}
		goal.Mul(&goal, &u)
	}
	return 0, errors.New("alpha pairing target outside bounded witness search")
}
