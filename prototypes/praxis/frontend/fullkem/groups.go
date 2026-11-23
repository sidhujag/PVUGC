package fullkem

import (
	"bytes"
	"errors"
	"io"
	"runtime"
	"sync"

	"github.com/consensys/gnark-crypto/ecc/bn254"
)

// At full width the same fixed bases are used tens of millions of times.
// Cache [digit * 256^window]G and sum the selected entries with gnark mixed
// Jacobian-affine additions. Small runs use gnark's native batch routine.
var initTables sync.Once
var base1 [32][256]bn254.G1Affine
var base2 [32][256]bn254.G2Affine

func initFixedTables() {
	var w1 bn254.G1Jac
	w1.FromAffine(&g1Base)
	var w2 bn254.G2Jac
	w2.FromAffine(&g2Base)
	for w := range base1 {
		var p1 bn254.G1Affine
		p1.FromJacobian(&w1)
		var p2 bn254.G2Affine
		p2.FromJacobian(&w2)
		var a bn254.G1Jac
		var b bn254.G2Jac
		for digit := 1; digit < 256; digit++ {
			a.AddMixed(&p1)
			b.AddMixed(&p2)
			base1[w][digit].FromJacobian(&a)
			base2[w][digit].FromJacobian(&b)
		}
		for range 8 {
			w1.DoubleAssign()
			w2.DoubleAssign()
		}
	}
}

func parallelRanges(n int, op func(start, end int) error) error {
	workers := min(runtime.GOMAXPROCS(0), (n+127)/128)
	if workers <= 1 {
		return op(0, n)
	}
	var wg sync.WaitGroup
	errs := make([]error, workers)
	for worker := range workers {
		wg.Add(1)
		go func(i int) { defer wg.Done(); errs[i] = op(i*n/workers, (i+1)*n/workers) }(worker)
	}
	wg.Wait()
	return errors.Join(errs...)
}

func fixedG1(s []scalar) []bn254.G1Affine {
	if len(s) < 128 {
		return bn254.BatchScalarMultiplicationG1(&g1Base, s)
	}
	initTables.Do(initFixedTables)
	p := make([]bn254.G1Jac, len(s))
	parallelRanges(len(s), func(start, end int) error {
		for i := start; i < end; i++ {
			limbs := s[i].Bits()
			for j, u := range limbs {
				for k := 0; k < 8; k++ {
					if d := byte(u); d != 0 {
						p[i].AddMixed(&base1[j*8+k][d])
					}
					u >>= 8
				}
			}
		}
		return nil
	})
	return bn254.BatchJacobianToAffineG1(p)
}

func fixedG2(s []scalar) []bn254.G2Affine {
	if len(s) < 128 {
		return bn254.BatchScalarMultiplicationG2(&g2Base, s)
	}
	initTables.Do(initFixedTables)
	out := make([]bn254.G2Affine, len(s))
	parallelRanges(len(s), func(start, end int) error {
		var acc bn254.G2Jac
		for i := start; i < end; i++ {
			acc.Z.SetZero()
			limbs := s[i].Bits()
			for j, u := range limbs {
				for k := 0; k < 8; k++ {
					if d := byte(u); d != 0 {
						acc.AddMixed(&base2[j*8+k][d])
					}
					u >>= 8
				}
			}
			out[i].FromJacobian(&acc)
		}
		return nil
	})
	return out
}
func writeG1(w io.Writer, s []scalar) error {
	points := fixedG1(s)
	buf := make([]byte, len(s)*32)
	for i := range points {
		b := points[i].Bytes()
		copy(buf[32*i:], b[:])
	}
	_, err := w.Write(buf)
	return err
}
func writeG2(w io.Writer, s []scalar) error {
	points := fixedG2(s)
	buf := make([]byte, len(s)*64)
	for i := range points {
		b := points[i].Bytes()
		copy(buf[64*i:], b[:])
	}
	_, err := w.Write(buf)
	return err
}

func readG1(r io.Reader, n int) ([]bn254.G1Affine, error) {
	points := make([]bn254.G1Affine, n)
	buf := make([]byte, n*32)
	if _, err := io.ReadFull(r, buf); err != nil {
		return nil, err
	}
	err := parallelRanges(n, func(start, end int) error {
		for i := start; i < end; i++ {
			b := buf[i*32 : (i+1)*32]
			if _, err := points[i].SetBytes(b); err != nil {
				return err
			}
			check := points[i].Bytes()
			if !bytes.Equal(check[:], b) {
				return errors.New("noncanonical G1 encoding")
			}
		}
		return nil
	})
	return points, err
}
func readG2(r io.Reader, n int) ([]bn254.G2Affine, error) {
	points := make([]bn254.G2Affine, n)
	buf := make([]byte, n*64)
	if _, err := io.ReadFull(r, buf); err != nil {
		return nil, err
	}
	err := parallelRanges(n, func(start, end int) error {
		for i := start; i < end; i++ {
			b := buf[i*64 : (i+1)*64]
			if _, err := points[i].SetBytes(b); err != nil {
				return err
			}
			check := points[i].Bytes()
			if !bytes.Equal(check[:], b) {
				return errors.New("noncanonical G2 encoding")
			}
		}
		return nil
	})
	return points, err
}
