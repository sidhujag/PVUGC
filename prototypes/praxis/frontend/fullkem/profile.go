// Package fullkem implements Praxis Figures 6 and 7 at the full input width,
// with a six-copy research grid (n=4, d_R=2, K1=1, K2=2, g=8, J=J'=1).
// This profile is intended for measuring honest recovery, with no security-level claim.
package fullkem

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
)

// Shape pins both public dimensions and the caller's commitment to the full public statement.
type Shape struct {
	N, D, Nu, CosetSize int
	Statement           [32]byte
}

// Evaluations contains public polynomials evaluated at a secret point. The
// constant wire precedes the N Boolean wires.
type Evaluations struct {
	A, B                 []fr.Element
	FullZ, Z, Z0, Corner fr.Element
}

// Openings contains ascending monomial coefficients, including the zero slots
// at multiples of Nu in Remainder. Trailing zero coefficients may be omitted.
type Openings struct{ KeyQ, OtherQ, Remainder []fr.Element }

const (
	blockWidth = 1024
	pointChunk = 16384
	g          = 8
	legs       = 6
	extraCount = 62
)

var legExp = [legs]int{0, 1, 0, 2, 3, 2}
var legKind = [legs]int{0, 1, 2, 0, 1, 2}
var one = fr.One()
var c0 = fft.GeneratorFullMultiplicativeGroup()
var omega = func() fr.Element {
	k := new(big.Int).Sub(fr.Modulus(), big.NewInt(1))
	k.Rsh(k, 2)
	var w fr.Element
	w.Exp(c0, k)
	return w
}()
var g1Base, g2Base = func() (bn254.G1Affine, bn254.G2Affine) { _, _, p, q := bn254.Generators(); return p, q }()
var gtBase = func() bn254.GT {
	v, err := bn254.Pair([]bn254.G1Affine{g1Base}, []bn254.G2Affine{g2Base})
	if err != nil {
		panic(err)
	}
	return v
}()

type scalar = fr.Element

func add(a, b scalar) (out scalar)              { out.Add(&a, &b); return }
func sub(a, b scalar) (out scalar)              { out.Sub(&a, &b); return }
func mul(a, b scalar) (out scalar)              { out.Mul(&a, &b); return }
func neg(a scalar) (out scalar)                 { out.Neg(&a); return }
func inv(a scalar) (out scalar)                 { out.Inverse(&a); return }
func asBig(a scalar) *big.Int                   { return a.BigInt(new(big.Int)) }
func fromInt(a int) scalar                      { return fr.NewElement(uint64(a)) }
func gtExp(a bn254.GT, b scalar) (out bn254.GT) { out.CyclotomicExp(a, asBig(b)); return }
func gtInt(a bn254.GT, b int) (out bn254.GT)    { out.CyclotomicExp(a, big.NewInt(int64(b))); return }

func (s Shape) validate() error {
	if s.N < 1 || s.D < 1 || s.Nu < 1 || s.CosetSize < 1 || uint64(s.D) > math.MaxUint32 ||
		uint64(s.N) > math.MaxUint32 || uint64(s.CosetSize) > math.MaxUint32 || s.Nu > s.CosetSize ||
		s.Nu&(s.Nu-1) != 0 || s.CosetSize%s.Nu != 0 || int64(s.D) != int64(s.N)+2+int64(s.CosetSize) {
		return errors.New("invalid full-width QAP dimensions")
	}
	return nil
}

func (s Shape) header() []byte {
	v := make([]byte, 56)
	copy(v, "PXKEM001")
	for i, n := range []int{s.N, s.D, s.Nu, s.CosetSize} {
		binary.BigEndian.PutUint32(v[8+i*4:], uint32(n))
	}
	copy(v[24:], s.Statement[:])
	return v
}

func WireBytes(s Shape) (int64, error) {
	if err := s.validate(); err != nil {
		return 0, err
	}
	n, c := int64(s.N), int64(s.CosetSize)
	return 56 + 64*(1+(n+1)/2) + 32*(3*(n+1)+int64(s.D)+c-c/int64(s.Nu)) + 64*(24*(n+1)+2*extraCount) + 384 + 13, nil
}

func blocks(n int, apply func(int, int) error) error {
	if err := apply(0, 1); err != nil {
		return err
	}
	for start := 1; start <= n; start += blockWidth {
		if err := apply(start, min(blockWidth, n+1-start)); err != nil {
			return err
		}
	}
	return nil
}
func checkHeader(r io.Reader, s Shape) error {
	var header [56]byte
	if _, err := io.ReadFull(r, header[:]); err != nil {
		return err
	}
	if !bytes.Equal(header[:], s.header()) {
		return errors.New("capsule profile, dimensions or statement commitment mismatch")
	}
	return nil
}
func eoi(r io.Reader) error {
	var extra [1]byte
	_, err := io.ReadFull(r, extra[:])
	if err == io.EOF {
		return nil
	}
	if err != nil {
		return err
	}
	return errors.New("trailing capsule bytes")
}
func validateOpenings(s Shape, o Openings) error {
	if len(o.KeyQ) > s.D || len(o.OtherQ) > s.D || len(o.Remainder) > s.CosetSize {
		return errors.New("QAP opening degree exceeds published powers")
	}
	for i := 0; i < len(o.Remainder); i += s.Nu {
		if !o.Remainder[i].IsZero() {
			return fmt.Errorf("forbidden remainder coefficient at %d", i)
		}
	}
	return nil
}
func seedMask(k bn254.GT, ctx [32]byte, in [13]byte) (out [13]byte) {
	h := sha256.New()
	h.Write([]byte("PVUGC/Praxis/BN254/fullwidth/H-key-100/v1"))
	h.Write(ctx[:])
	b := k.Bytes()
	h.Write(b[:])
	mask := h.Sum(nil)
	for i := range out {
		out[i] = in[i] ^ mask[i]
	}
	out[12] &= 0xf0
	return
}
func expandSeed(seed [13]byte, ctx [32]byte) [32]byte {
	h := sha256.New()
	h.Write([]byte("PVUGC/Praxis/BN254/fullwidth/DEM-seed-100/v1"))
	h.Write(ctx[:])
	h.Write(seed[:])
	var out [32]byte
	copy(out[:], h.Sum(nil))
	return out
}
