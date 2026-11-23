package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"pvugc.example/praxis-frontend/fullrows"
)

func put(t *testing.T, path string, data []byte) {
	t.Helper()
	if err := os.WriteFile(path, data, 0600); err != nil {
		t.Fatal(err)
	}
}

func read(t *testing.T, path string) []byte {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func missing(t *testing.T, path string) {
	t.Helper()
	if _, err := os.Lstat(path); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("expected %s to be absent, got %v", path, err)
	}
}

func TestSignatureEnvelope(t *testing.T) {
	dir := t.TempDir()
	path := func(name string) string { return filepath.Join(dir, name) }
	// This genuine v2 row enforces x=y over two Boolean wires: 00 and 11 pass.
	rows := []byte("[\"plain\",[[1,0,1,-1,0],[-1,1,1,-1,0]]]\n")
	put(t, path("rows.jsonl"), rows)
	digest := sha256.Sum256(append([]byte("PVUGC affine-product BQS v2\n"), rows...))
	manifest, err := json.Marshal(map[string]any{
		"format": fullrows.Format, "fr": fr.Modulus().String(),
		"unknowns": 2, "constraints": 1, "max_products": 2,
		"recipe_bytes": len(rows), "digest": fmt.Sprintf("%x", digest),
	})
	if err != nil {
		t.Fatal(err)
	}
	put(t, path("manifest.json"), manifest)
	s, err := load(path("manifest.json"), path("rows.jsonl"))
	if err != nil {
		t.Fatal(err)
	}
	// SIGHASH_ALL signature from the Rust synthetic cancel fixture. These
	// tests exercise opaque payload transport; Bitcoin verification is separate.
	signature, err := hex.DecodeString("3676efa6460d9d2438308a83beb49544710be65d2125a994ea94cce30eb34c2c49485a88d68d705c0ca735c331eb1313ada3d72a8d2e676fb09f9a1148eaa8fa01")
	if err != nil {
		t.Fatal(err)
	}
	put(t, path("signature"), signature)
	pin, err := arm(s, path("signature"), path("capsule"))
	if err != nil {
		t.Fatal(err)
	}
	wire := read(t, path("capsule"))
	actual := sha256.Sum256(wire)
	if !bytes.Equal(actual[:], pin) {
		t.Fatal("arming receipt differs from the published envelope hash")
	}
	witness := path("witness")
	openCLI := func(capsulePath string, h []byte, dst string) error {
		return run([]string{"open", path("manifest.json"), path("rows.jsonl"), capsulePath, hex.EncodeToString(h), witness, dst})
	}
	for _, v := range []byte{0, 3} {
		put(t, witness, []byte{v})
		out := path(fmt.Sprintf("signature-%d", v))
		if err := openCLI(path("capsule"), pin, out); err != nil {
			t.Fatalf("packed witness %d: %v", v, err)
		}
		if !bytes.Equal(read(t, out), signature) {
			t.Fatalf("packed witness %d recovered different bytes", v)
		}
	}
	t.Run("64-byte default sighash payload", func(t *testing.T) {
		// The envelope transports opaque bytes. A default-length payload carries
		// no trailing sighash byte, including when its final byte is zero.
		payload := bytes.Repeat([]byte{0x80, 0xff, 0x01, 0x00}, 16)
		put(t, path("default-payload"), payload)
		capsule := path("default-capsule")
		defaultPin, err := arm(s, path("default-payload"), capsule)
		if err != nil {
			t.Fatal(err)
		}
		put(t, witness, []byte{3})
		output := path("default-output")
		if err := openCLI(capsule, defaultPin, output); err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(read(t, output), payload) {
			t.Fatal("64-byte payload changed during recovery")
		}
	})
	// Wrong receipt, then changed GCM tag with a matching new file receipt.
	wrong := append([]byte(nil), pin...)
	wrong[0] ^= 1
	if err := openCLI(path("capsule"), wrong, path("wrong-pin")); err == nil || !strings.Contains(err.Error(), "receipt mismatch") {
		t.Fatalf("wrong receipt returned %v", err)
	}
	missing(t, path("wrong-pin"))
	tampered := append([]byte(nil), wire...)
	tampered[len(tampered)-1] ^= 1
	put(t, path("bad-capsule"), tampered)
	newPin := sha256.Sum256(tampered)
	if err := openCLI(path("bad-capsule"), newPin[:], path("bad-tag")); err == nil || !strings.Contains(err.Error(), "authentication failed") {
		t.Fatalf("modified GCM tag with refreshed file digest returned %v", err)
	}
	missing(t, path("bad-tag"))
	put(t, witness, []byte{1})
	if err := openCLI(path("capsule"), pin, path("bad-witness")); err == nil {
		t.Fatal("unsatisfied assignment accepted")
	}
	missing(t, path("bad-witness"))
	put(t, witness, []byte{3})
	put(t, path("existing"), []byte("preexisting bytes"))
	if err := openCLI(path("capsule"), pin, path("existing")); err == nil {
		t.Fatal("overwrote existing output")
	}
	if string(read(t, path("existing"))) != "preexisting bytes" {
		t.Fatal("changed existing output on failure")
	}
	armArgs := []string{"arm", path("manifest.json"), path("rows.jsonl"), path("signature"), path("capsule")}
	if err := run(armArgs); err == nil || !bytes.Equal(wire, read(t, path("capsule"))) {
		t.Fatal("arming accepted or altered an existing capsule")
	}
	put(t, path("signature"), make([]byte, 66))
	armArgs[4] = path("bad-length")
	if err := run(armArgs); err == nil {
		t.Fatal("accepted 66-byte signature")
	}
	missing(t, path("bad-length"))
}

func TestPublishFailureLeavesNoOutput(t *testing.T) {
	dir := t.TempDir()
	dst := filepath.Join(dir, "published")
	fail := errors.New("interrupted write")
	err := publish(dst, func(f *os.File) error {
		if _, err := f.Write([]byte("partial")); err != nil {
			return err
		}
		return fail
	})
	if !errors.Is(err, fail) {
		t.Fatal(err)
	}
	missing(t, dst)
	// Simulate another creator winning between the initial Lstat and Link.
	err = publish(dst, func(f *os.File) error {
		if _, err := f.Write([]byte("ours")); err != nil {
			return err
		}
		return os.WriteFile(dst, []byte("other publisher"), 0600)
	})
	if !errors.Is(err, os.ErrExist) || string(read(t, dst)) != "other publisher" {
		t.Fatalf("lost publish race changed the destination or returned %v", err)
	}
	entries, err := os.ReadDir(dir)
	if err != nil || len(entries) != 1 || entries[0].Name() != "published" {
		t.Fatalf("publish left partial files: %v (%v)", entries, err)
	}
}
