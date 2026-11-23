package fullqap

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"pvugc.example/praxis-frontend/fullrows"
)

func smallSystem(t *testing.T, n int) *fullrows.System {
	t.Helper()
	recipes := strings.Join([]string{
		`["plain",[[1,0,1,-1,0],[-1,1,1,-1,0]]]`, // x - y
		`["plain",[[1,0,1,1,1],[-1,0,1,-1,0]]]`,  // xy - x
		`["plain",[[1,1,1,1,1],[-1,1,1,-1,0]]]`,  // y*y - y
	}, "\n") + "\n"
	digest := sha256.Sum256([]byte("PVUGC affine-product BQS v2\n" + recipes))
	manifest, err := json.Marshal(map[string]any{"format": fullrows.Format, "fr": fr.Modulus().String(), "unknowns": n, "constraints": 3, "max_products": 2, "recipe_bytes": len(recipes), "digest": hex.EncodeToString(digest[:])})
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	m, r := filepath.Join(dir, "manifest.json"), filepath.Join(dir, "recipe.jsonl")
	if err = os.WriteFile(m, manifest, 0600); err != nil {
		t.Fatal(err)
	}
	if err = os.WriteFile(r, []byte(recipes), 0600); err != nil {
		t.Fatal(err)
	}
	s, err := fullrows.Open(m, r)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func productAt(x fr.Element, points []fr.Element) fr.Element {
	y := fr.One()
	for i := range points {
		var t fr.Element
		t.Sub(&x, &points[i])
		y.Mul(&y, &t)
	}
	return y
}

func lagrangeDirect(x fr.Element, points []fr.Element, index int) fr.Element {
	n, d := fr.One(), fr.One()
	for i := range points {
		if i != index {
			var u, v fr.Element
			u.Sub(&x, &points[i])
			v.Sub(&points[index], &points[i])
			n.Mul(&n, &u)
			d.Mul(&d, &v)
		}
	}
	n.Div(&n, &d)
	return n
}

func polynomialAt(coeff []fr.Element, x fr.Element) fr.Element {
	var y fr.Element
	for i := len(coeff) - 1; i >= 0; i-- {
		y.Mul(&y, &x).Add(&y, &coeff[i])
	}
	return y
}

func TestDirectEquationAndSetup(t *testing.T) {
	// D=16 and D=19 cover no holes, a proper complement, non-power-of-two
	// row count, irregular P0 endpoints, and a quotient with both corner cases.
	for _, n := range []int{2, 5} {
		d, err := New(n, 3, 4)
		if err != nil {
			t.Fatal(err)
		}
		s := smallSystem(t, n)
		points := d.roots[:d.D]
		for row := 0; row < d.Rows; row++ {
			constant := new(fr.Element).Exp(points[row*d.Nu], big.NewInt(int64(d.Nu)))
			for j := 1; j < d.Nu; j++ {
				test := new(fr.Element).Exp(points[row*d.Nu+j], big.NewInt(int64(d.Nu)))
				if !test.Equal(constant) {
					t.Fatalf("row %d is not a coset", row)
				}
			}
		}
		tau := fr.NewElement(42)
		setup, err := d.Setup(tau, s)
		if err != nil {
			t.Fatal(err)
		}
		corner := lagrangeDirect(tau, points, d.D-1)
		if setup.FullZ != productAt(tau, points) || setup.Z != productAt(tau, points[:d.D-1]) || setup.Z0 != productAt(tau, points[d.CosetSize:]) || setup.Corner != corner {
			t.Fatal("vanishing factors or corner differ")
		}
		l := make([]fr.Element, d.D)
		for i := range l {
			l[i] = lagrangeDirect(tau, points, i)
		}
		a, b := make([]fr.Element, n+1), make([]fr.Element, n+1)
		a[0], b[0] = corner, corner
		b[0].Add(&b[0], &l[d.CosetSize])
		for i := 1; i <= n; i++ {
			a[i], b[i] = l[d.CosetSize+i], l[d.CosetSize+i]
			a[0].Sub(&a[0], &l[d.CosetSize+i])
		}
		addLeft := func(slot, wire int) {
			z0 := productAt(points[slot], points[d.CosetSize:])
			z0.Mul(&z0, &l[slot])
			a[wire].Add(&a[wire], &z0)
		}
		addLeft(0, 1)
		addLeft(1, 2)
		b[0].Add(&b[0], &l[0]).Sub(&b[0], &l[1])
		addLeft(4, 1)
		b[2].Add(&b[2], &l[4])
		b[0].Sub(&b[0], &l[4])
		addLeft(8, 2)
		b[2].Add(&b[2], &l[8])
		b[0].Sub(&b[0], &l[8])
		for _, slot := range []int{3, 7, 11} {
			addLeft(slot, 0)
		}
		for i := range a {
			if a[i] != setup.A[i] || b[i] != setup.B[i] {
				t.Fatalf("wire %d differs from direct interpolation", i)
			}
		}
		if _, err := d.Setup(points[0], s); err == nil {
			t.Fatal("sampling at used point accepted")
		}
		if len(d.roots) > d.D {
			if _, err := d.Setup(d.roots[d.D], s); err != nil {
				t.Fatal("valid unused ambient point", err)
			}
		}
		for _, w := range []byte{0, 3} {
			op, err := d.Open([]byte{w}, s)
			if err != nil {
				t.Fatal(err)
			}
			if len(op.KeyQ) != d.D-1 || len(op.OtherQ) != d.D || len(op.Remainder) != d.CosetSize {
				t.Fatal("wrong polynomial bounds")
			}
			// Check both complete polynomial identities on > 2D-2 distinct
			// field elements using independent Lagrange sums over ALL points.
			av, bv, rv := make([]fr.Element, d.D), make([]fr.Element, d.D), make([]fr.Element, d.CosetSize)
			bit := fr.NewElement(uint64(w & 1))
			one := fr.One()
			av[d.D-1], bv[d.D-1], bv[d.CosetSize] = one, one, one
			for i := range n {
				wire := fr.NewElement(uint64(w >> i & 1))
				at := d.CosetSize + 1 + i
				av[at].Sub(&wire, &one)
				bv[at] = wire
			}
			for _, slot := range []int{0, 1, 4, 8} {
				z0 := productAt(points[slot], points[d.CosetSize:])
				av[slot].Mul(&bit, &z0)
			}
			bv[0] = one
			bv[1].Neg(&one)
			bv[4].Sub(&bit, &one)
			bv[8].Sub(&bit, &one)
			for i := range rv {
				z0 := productAt(points[i], points[d.CosetSize:])
				rv[i].Mul(&av[i], &bv[i]).Div(&rv[i], &z0)
				if polynomialAt(op.Remainder, points[i]) != rv[i] {
					t.Fatalf("remainder differs at slot %d", i)
				}
			}
			for _, slot := range []int{3, 7, 11} {
				av[slot] = productAt(points[slot], points[d.CosetSize:])
			}
			for j := 0; j < 2*d.D; j++ {
				x := fr.NewElement(uint64(j + 50))
				var aw, bw, term fr.Element
				for i := range points {
					weight := lagrangeDirect(x, points, i)
					term.Mul(&av[i], &weight)
					aw.Add(&aw, &term)
					term.Mul(&bv[i], &weight)
					bw.Add(&bw, &term)
				}
				z0 := productAt(x, points[d.CosetSize:])
				rz := polynomialAt(op.Remainder, x)
				rz.Mul(&rz, &z0)
				corner := lagrangeDirect(x, points, d.D-1)
				p := aw
				p.Mul(&p, &bw)
				full := productAt(x, points)
				key := polynomialAt(op.KeyQ, x)
				key.Mul(&key, &full).Add(&key, &rz).Add(&key, &corner)
				z := productAt(x, points[:d.D-1])
				other := polynomialAt(op.OtherQ, x)
				other.Mul(&other, &z).Add(&other, &rz)
				if p != key || p != other {
					t.Fatalf("equation (4) failed for n=%d,w=%d,x=%d", n, w, j+50)
				}
			}
		}
		if _, err := d.Open([]byte{1}, s); err == nil {
			t.Fatal("unsatisfied row accepted")
		}
		if _, err := d.Open([]byte{255}, s); err == nil {
			t.Fatal("noncanonical padding accepted")
		}
	}
}
