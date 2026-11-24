// shared-pay measures the single-table, pinned-receipt fixture. All coins,
// outpoints, scripts and signing material are synthetic.
package main

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"time"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"pvugc.example/praxis-frontend/fullrows"
	"pvugc.example/praxis-frontend/payselector"
	"pvugc.example/praxis-frontend/scratch"
)

const archiveTag = "PXSPAY01"
const width = 3
const metadataLimit = 1 << 17

type specification struct {
	Signer payselector.Identity
	Pay    payselector.Pay
}

type envelope struct {
	Spec    specification
	Packets [payselector.PacketCount][]byte
}

func fixturePay() payselector.Pay {
	reserve := chainhash.DoubleHashH([]byte("PVUGC shared Pay fixture reserve"))
	closeHash := chainhash.DoubleHashH([]byte("PVUGC shared Pay fixture close"))
	script := func(name string) []byte {
		hash := sha256.Sum256([]byte(name))
		return append([]byte{0x00, 0x14}, hash[:20]...)
	}
	return payselector.Pay{
		Reserve: wire.OutPoint{Hash: reserve, Index: 1}, Close: wire.OutPoint{Hash: closeHash, Index: 0},
		ReserveValue: 100000000, CloseValue: 10000, RecipientValue: 75000000, Fee: 2000,
		RecipientScript: script("regtest John"), ChangeScript: script("regtest change"), CloseScript: script("regtest close"),
	}
}

func layout(spec specification) (*scratch.Relation, []int, []byte, [32]byte, error) {
	digest, err := spec.Pay.Digest(spec.Signer)
	if err != nil {
		return nil, nil, nil, digest, err
	}
	slots := payselector.Selected(spec.Signer, digest)
	flags := make([]bool, payselector.PacketCount)
	witness := make([]byte, (len(flags)*(1+width)+7)/8)
	for _, slot := range slots {
		flags[slot] = true
		witness[slot/8] |= 1 << uint(slot%8)
	}
	rows, err := fullrows.NewPinnedScratch(flags, width)
	if err != nil {
		return nil, nil, nil, digest, err
	}
	relation, err := scratch.New(rows)
	return relation, slots, witness, digest, err
}

func scratchIndices(slots []int) []int {
	indices := make([]int, 0, width*len(slots))
	for _, slot := range slots {
		for j := range width {
			indices = append(indices, payselector.PacketCount+slot*width+j)
		}
	}
	return indices
}

func context(spec specification, table []byte) ([32]byte, error) {
	desc, err := json.Marshal(spec)
	if err != nil {
		return [32]byte{}, err
	}
	h := sha256.New()
	h.Write([]byte("PVUGC/shared-pay/fixture-v1/regtest/reserve-input-0"))
	tableHash := sha256.Sum256(table)
	h.Write(tableHash[:])
	h.Write(desc)
	var result [32]byte
	copy(result[:], h.Sum(nil))
	return result, nil
}

// Each development coordinate has eight values. Authentication detects
// accidental corruption; a three-coordinate tuple has only nine bits of entropy.
func packetCipher(ctx [32]byte, slot int, tuple []byte) (cipher.AEAD, []byte, error) {
	if slot < 0 || slot >= payselector.PacketCount || len(tuple) != width {
		return nil, nil, errors.New("invalid slot or tuple width")
	}
	for _, u := range tuple {
		if u < 2 || u > 9 {
			return nil, nil, errors.New("coordinate outside development profile")
		}
	}
	aad := binary.BigEndian.AppendUint16(append([]byte(nil), ctx[:]...), uint16(slot))
	h := sha256.New()
	h.Write([]byte("PVUGC/shared-pay/fixture-v1/packet-key"))
	h.Write(aad)
	h.Write(tuple)
	key := h.Sum(nil)
	defer clear(key)
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, nil, err
	}
	aead, err := cipher.NewGCMWithRandomNonce(block)
	return aead, aad, err
}

type receipt struct {
	size int
	hash [sha256.Size]byte
}

func writeArchive(path string, env envelope, table []byte) (receipt, error) {
	desc, err := json.Marshal(env)
	if err != nil {
		return receipt{}, err
	}
	if len(desc) > metadataLimit {
		return receipt{}, errors.New("descriptor exceeds fixture limit")
	}
	// Publish by linking a finished file, so retries cannot overwrite an
	// existing archive and a partial write cannot appear at the target path.
	f, err := os.CreateTemp(filepath.Dir(path), ".pvugc-shared-pay-*")
	if err != nil {
		return receipt{}, err
	}
	defer os.Remove(f.Name())
	defer f.Close()
	header := binary.BigEndian.AppendUint32([]byte(archiveTag), uint32(len(desc)))
	h := sha256.New()
	writer := io.MultiWriter(f, h)
	for _, part := range [][]byte{header, desc, table} {
		if _, err := writer.Write(part); err != nil {
			return receipt{}, err
		}
	}
	if err := f.Close(); err != nil {
		return receipt{}, err
	}
	r := receipt{size: len(header) + len(desc) + len(table)}
	copy(r.hash[:], h.Sum(nil))
	return r, os.Link(f.Name(), path)
}

func arm(path string) error {
	signer, packets, err := payselector.ArmFixture()
	if err != nil {
		return err
	}
	defer func() {
		for i := range packets {
			clear(packets[i])
		}
	}()
	env := envelope{Spec: specification{Signer: signer, Pay: fixturePay()}}
	relation, _, _, _, err := layout(env.Spec)
	if err != nil {
		return err
	}
	slots := make([]int, len(packets))
	for i := range slots {
		slots[i] = i
	}
	var table bytes.Buffer
	tuples, err := relation.Arm(&table, scratchIndices(slots))
	if err != nil {
		return err
	}
	defer clear(tuples)
	ctx, err := context(env.Spec, table.Bytes())
	if err != nil {
		return err
	}
	var payload, wrapped int
	for i, packet := range packets {
		aead, aad, err := packetCipher(ctx, i, tuples[i*width:(i+1)*width])
		if err != nil {
			return err
		}
		env.Packets[i] = aead.Seal(nil, nil, packet, aad)
		payload += len(packet)
		wrapped += len(env.Packets[i])
	}
	r, err := writeArchive(path, env, table.Bytes())
	if err == nil {
		fmt.Printf("arm table_bytes=%d plaintext_bytes=%d sealed_packet_bytes=%d archive_bytes=%d archive_sha256=%x\n", table.Len(), payload, wrapped, r.size, r.hash)
	}
	return err
}

func open(path string, expected [sha256.Size]byte) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	h := sha256.New()
	src := io.TeeReader(f, h)
	var header [len(archiveTag) + 4]byte
	if _, err := io.ReadFull(src, header[:]); err != nil {
		return err
	}
	n := binary.BigEndian.Uint32(header[len(archiveTag):])
	if string(header[:len(archiveTag)]) != archiveTag || n == 0 || n > metadataLimit {
		return errors.New("invalid shared Pay archive header")
	}
	desc := make([]byte, n)
	if _, err := io.ReadFull(src, desc); err != nil {
		return err
	}
	var env envelope
	if err := json.Unmarshal(desc, &env); err != nil {
		return err
	}
	canonical, err := json.Marshal(env)
	if err != nil || !bytes.Equal(canonical, desc) {
		return errors.New("noncanonical shared Pay archive descriptor")
	}
	relation, slots, witness, digest, err := layout(env.Spec)
	if err != nil {
		return err
	}
	size, err := relation.WireBytes()
	if err != nil {
		return err
	}
	table, err := io.ReadAll(io.LimitReader(src, size+1))
	if err != nil || int64(len(table)) != size {
		return errors.New("truncated or extended factor table")
	}
	if !bytes.Equal(expected[:], h.Sum(nil)) {
		return errors.New("archive differs from pinned setup receipt")
	}
	ctx, err := context(env.Spec, table)
	if err != nil {
		return err
	}
	coords, err := relation.Coordinates(bytes.NewReader(table), witness, scratchIndices(slots))
	if err != nil {
		return err
	}
	defer clear(coords)
	opened := make(map[int][]byte, len(slots))
	defer func() {
		for _, packet := range opened {
			clear(packet)
		}
	}()
	for j, i := range slots {
		aead, aad, err := packetCipher(ctx, i, coords[j*width:(j+1)*width])
		if err != nil {
			return err
		}
		opened[i], err = aead.Open(nil, nil, env.Packets[i], aad)
		if err != nil {
			return fmt.Errorf("slot %d failed authentication: %w", i, err)
		}
	}
	sig, err := payselector.Signature(env.Spec.Signer, digest, opened)
	if err != nil {
		return err
	}
	if err := env.Spec.Pay.Verify(env.Spec.Signer, sig); err != nil {
		return err
	}
	fmt.Printf("open selected_slots=%d native_searches=%d digest=%x signature=%s reserve_input_verified=true\n", len(slots), 1+width*len(slots), digest, hex.EncodeToString(sig[:]))
	return nil
}

func main() {
	arming := len(os.Args) == 3 && os.Args[1] == "arm"
	opening := len(os.Args) == 4 && os.Args[1] == "open"
	if !arming && !opening {
		fmt.Fprintln(os.Stderr, "usage: shared-pay arm ARCHIVE | shared-pay open ARCHIVE EXPECTED_SHA256")
		os.Exit(2)
	}
	start := time.Now()
	var err error
	if arming {
		err = arm(os.Args[2])
	} else {
		var pin []byte
		pin, err = hex.DecodeString(os.Args[3])
		if err == nil && len(pin) != sha256.Size {
			err = errors.New("archive pin must be a 32-byte SHA-256 digest")
		}
		if err == nil {
			err = open(os.Args[2], [sha256.Size]byte(pin))
		}
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Printf("elapsed=%s\n", time.Since(start).Round(time.Millisecond))
}
