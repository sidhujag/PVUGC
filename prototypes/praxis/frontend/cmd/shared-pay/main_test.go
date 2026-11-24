package main

import (
	"bytes"
	"crypto/sha256"
	"os"
	"path/filepath"
	"testing"
)

func TestPacketBinding(t *testing.T) {
	ctx := sha256.Sum256([]byte("fixture A"))
	tuple := []byte{2, 5, 9}
	aead, aad, err := packetCipher(ctx, 19, tuple)
	if err != nil {
		t.Fatal(err)
	}
	payload := bytes.Repeat([]byte{42}, 32)
	packet := aead.Seal(nil, nil, payload, aad)
	opened, err := aead.Open(nil, nil, packet, aad)
	if err != nil || !bytes.Equal(opened, payload) {
		t.Fatal("fixture packet did not round-trip")
	}
	other, otherAAD, err := packetCipher(ctx, 20, tuple)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := other.Open(nil, nil, packet, otherAAD); err == nil {
		t.Fatal("packet accepted under a different slot")
	}
	packet[len(packet)-1] ^= 1
	if _, err := aead.Open(nil, nil, packet, aad); err == nil {
		t.Fatal("damaged packet accepted")
	}
}

func TestArchivePublicationAndTruncation(t *testing.T) {
	path := filepath.Join(t.TempDir(), "receipt.px")
	if _, err := writeArchive(path, envelope{}, []byte{1}); err != nil {
		t.Fatal(err)
	}
	first, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := writeArchive(path, envelope{}, []byte{2}); err == nil {
		t.Fatal("existing fixture replaced")
	}
	still, err := os.ReadFile(path)
	if err != nil || !bytes.Equal(first, still) {
		t.Fatal("existing fixture changed")
	}
	if err := os.WriteFile(path, first[:len(archiveTag)+2], 0600); err != nil {
		t.Fatal(err)
	}
	if err := open(path, [32]byte{}); err == nil {
		t.Fatal("truncated header accepted")
	}
}
