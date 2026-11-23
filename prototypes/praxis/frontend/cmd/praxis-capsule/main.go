// praxis-capsule arms or opens a full-verifier, development-profile cancellation capsule.
package main

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math/bits"
	"os"
	"path/filepath"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"pvugc.example/praxis-frontend/fullkem"
	"pvugc.example/praxis-frontend/fullqap"
	"pvugc.example/praxis-frontend/fullrows"
)

const magic = "PXCAN001"
const headerBytes = len(magic) + 1 + 12

type statement struct {
	system *fullrows.System
	domain *fullqap.Domain
	shape  fullkem.Shape
}

func load(manifest, rows string) (*statement, error) {
	s, err := fullrows.Open(manifest, rows)
	if err != nil {
		return nil, err
	}
	nu := 1 << bits.Len(uint(s.MaxProducts))
	d, err := fullqap.New(s.Unknowns, len(s.Rows), nu)
	if err != nil {
		return nil, err
	}
	return &statement{s, d, fullkem.Shape{N: d.N, D: d.D, Nu: d.Nu, CosetSize: d.CosetSize, Statement: s.ManifestHash}}, nil
}

// The target becomes visible only after the full write succeeds. Link refuses to clobber it.
func publish(path string, write func(*os.File) error) error {
	if _, err := os.Lstat(path); !os.IsNotExist(err) {
		if err != nil {
			return err
		}
		return fmt.Errorf("destination already exists: %s", path)
	}
	f, err := os.CreateTemp(filepath.Dir(path), ".praxis-pending-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	defer f.Close()
	if err := write(f); err != nil {
		return err
	}
	if err := f.Sync(); err != nil {
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	return os.Link(f.Name(), path)
}

func gcm(key [32]byte) (cipher.AEAD, error) {
	block, err := aes.NewCipher(key[:])
	if err != nil {
		return nil, err
	}
	return cipher.NewGCM(block)
}

func arm(s *statement, signature, path string) ([]byte, error) {
	f, err := os.Open(signature)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	sig, err := io.ReadAll(io.LimitReader(f, 66))
	if err != nil {
		return nil, err
	}
	if len(sig) != 64 && len(sig) != 65 {
		return nil, errors.New("expected a 64- or 65-byte Taproot signature")
	}
	var header [headerBytes]byte
	copy(header[:], magic)
	header[len(magic)] = byte(len(sig))
	nonce := header[len(magic)+1:]
	if _, err := rand.Read(nonce); err != nil {
		return nil, err
	}
	hash := sha256.New()
	err = publish(path, func(file *os.File) error {
		out := io.MultiWriter(file, hash)
		if _, err := out.Write(header[:]); err != nil {
			return err
		}
		key, err := fullkem.Encrypt(out, s.shape, func(tau fr.Element) (fullkem.Evaluations, error) {
			q, err := s.domain.Setup(tau, s.system)
			if errors.Is(err, fullqap.ErrDomainPoint) {
				return fullkem.Evaluations{}, fullkem.ErrDomainPoint
			}
			if err != nil {
				return fullkem.Evaluations{}, err
			}
			return fullkem.Evaluations{A: q.A, B: q.B, FullZ: q.FullZ, Z: q.Z, Z0: q.Z0, Corner: q.Corner}, nil
		})
		if err != nil {
			return err
		}
		defer clear(key[:])
		a, err := gcm(key)
		if err != nil {
			return err
		}
		_, err = out.Write(a.Seal(nil, nonce, sig, append(header[:], s.shape.Statement[:]...)))
		return err
	})
	if err != nil {
		return nil, err
	}
	return hash.Sum(nil), nil
}

func open(s *statement, capsule, receipt, witness, path string) error {
	pin, err := hex.DecodeString(receipt)
	if err != nil || len(pin) != sha256.Size {
		return errors.New("expected the arming receipt in hex")
	}
	f, err := os.Open(capsule)
	if err != nil {
		return err
	}
	defer f.Close()
	kemBytes, err := fullkem.WireBytes(s.shape)
	if err != nil {
		return err
	}
	info, err := f.Stat()
	if err != nil {
		return err
	}
	base := int64(headerBytes+16) + kemBytes
	if info.Size() != base+64 && info.Size() != base+65 {
		return errors.New("incorrect capsule size")
	}
	hash := sha256.New()
	if _, err := io.Copy(hash, f); err != nil {
		return err
	}
	if !bytes.Equal(hash.Sum(nil), pin) {
		return errors.New("capsule receipt mismatch")
	}
	if _, err := f.Seek(0, io.SeekStart); err != nil {
		return err
	}
	hash.Reset()
	src := io.TeeReader(f, hash)
	var header [headerBytes]byte
	if _, err := io.ReadFull(src, header[:]); err != nil {
		return err
	}
	if string(header[:len(magic)]) != magic || int64(header[len(magic)]) != info.Size()-base {
		return errors.New("invalid signature capsule header")
	}
	w, err := os.Open(witness)
	if err != nil {
		return err
	}
	defer w.Close()
	packed, err := io.ReadAll(io.LimitReader(w, int64((s.shape.N+7)/8+1)))
	if err != nil {
		return err
	}
	o, err := s.domain.Open(packed, s.system)
	if err != nil {
		return err
	}
	bools := make([]bool, s.shape.N)
	for i := range bools {
		bools[i] = packed[i/8]&(1<<uint(i%8)) != 0
	}
	key, err := fullkem.Decrypt(io.LimitReader(src, kemBytes), s.shape, bools, fullkem.Openings{KeyQ: o.KeyQ, OtherQ: o.OtherQ, Remainder: o.Remainder})
	if err != nil {
		return err
	}
	defer clear(key[:])
	a, err := gcm(key)
	if err != nil {
		return err
	}
	sealed := make([]byte, int(header[len(magic)])+a.Overhead())
	if _, err := io.ReadFull(src, sealed); err != nil {
		return err
	}
	if !bytes.Equal(hash.Sum(nil), pin) {
		return errors.New("capsule changed during recovery")
	}
	sig, err := a.Open(nil, header[len(magic)+1:], sealed, append(header[:], s.shape.Statement[:]...))
	if err != nil {
		return err
	}
	return publish(path, func(out *os.File) error { _, err := out.Write(sig); return err })
}

func run(args []string) error {
	if (len(args) != 5 || args[0] != "arm") && (len(args) != 7 || args[0] != "open") {
		return errors.New("usage: praxis-capsule arm MANIFEST ROWS SIGNATURE CAPSULE | open MANIFEST ROWS CAPSULE RECEIPT WITNESS OUTPUT")
	}
	s, err := load(args[1], args[2])
	if err != nil {
		return err
	}
	if args[0] == "arm" {
		h, err := arm(s, args[3], args[4])
		if err != nil {
			return err
		}
		fmt.Printf("%x\n", h)
		return nil
	}
	return open(s, args[3], args[4], args[5], args[6])
}

func main() {
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
