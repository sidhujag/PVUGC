package guardednonce

import (
	"crypto/rand"
	"crypto/sha256"
	"crypto/sha3"
	"crypto/subtle"
	"encoding/binary"
	"testing"
)

type stateLabel [32]byte
type grantedState struct {
	bit   byte
	label stateLabel
}

// wire contains only fixed-layout ciphertexts and 32-byte authentication
// tags. The public setup, deterministic layout and secret label bank are
// separate. No key-delivery mechanism is implemented by this archive.
type gateRows struct {
	wire   []byte
	scope  [32]byte
	layout xorLayout
}

func gateScope(setup Setup) [32]byte {
	h := sha256.New()
	h.Write([]byte("PVUGC/guarded-nonce/512-xor-gate-archive/v1"))
	h.Write(setup.Context[:])
	h.Write(setup.Key[:])
	h.Write(setup.H[:])
	for j := range setup.C {
		h.Write(setup.C[j][:])
		h.Write(setup.T[j][:])
	}
	return [32]byte(h.Sum(nil))
}

// scope, gate, ordered wires, pattern and three labels are fixed width. The
// two independent domains distinguish the encryption pad and the MAC tag.
func rowXOF(tag bool, scope [32]byte, index int, gate xorGate, pattern byte, labels [3]stateLabel, ciphertext, output []byte) {
	h := sha3.NewSHAKE256()
	if tag {
		h.Write([]byte("PVUGC/guarded-nonce/row-tag/v1\x00"))
	} else {
		h.Write([]byte("PVUGC/guarded-nonce/row-pad/v1\x00"))
	}
	h.Write(scope[:])
	var fields [17]byte
	binary.BigEndian.PutUint32(fields[:4], uint32(index))
	for j, w := range gate {
		binary.BigEndian.PutUint32(fields[4+4*j:], uint32(w))
	}
	fields[16] = pattern
	h.Write(fields[:])
	for j := range labels {
		h.Write(labels[j][:])
	}
	if tag {
		h.Write(ciphertext)
	}
	h.Read(output)
}

func (l xorLayout) isDigestGate(i int) bool {
	return i >= l.digestStart && i < l.digestStart+len(l.digestGates)
}

func (l xorLayout) offset(i int) int {
	// Four 64-byte packets per gate, with two extra scalars per digest row.
	digestBefore := min(max(i-l.digestStart, 0), len(l.digestGates))
	return 4 * 64 * (i + digestBefore)
}

func sealGateRows(t *testing.T, layout xorLayout, dealer *Dealer) (gateRows, [][2]stateLabel) {
	t.Helper()
	bank := make([][2]stateLabel, layout.wires)
	for w := range bank {
		for state := range bank[w] {
			if _, err := rand.Read(bank[w][state][:]); err != nil {
				t.Fatal(err)
			}
		}
	}
	b := armChannel(t, layout.digestGates, layout.wires, dealer.b, nil)
	z := armChannel(t, layout.digestGates, layout.wires, dealer.rho, nil)
	signing := armChannel(t, layout.gates, layout.wires, dealer.k, &dealer.x)
	rows := gateRows{scope: gateScope(dealer.Public()), layout: layout, wire: make([]byte, layout.offset(len(layout.gates)))}
	for i, gate := range layout.gates {
		width := (layout.offset(i+1) - layout.offset(i)) / 4
		for pattern := range 4 {
			a, q := pattern>>1, pattern&1
			labels := [3]stateLabel{bank[gate[0]][a], bank[gate[1]][q], bank[gate[2]][a^q]}
			start := layout.offset(i) + pattern*width
			packet := rows.wire[start : start+width]
			ciphertext, tag := packet[:width-32], packet[width-32:]
			var plain [96]byte
			if layout.isDigestGate(i) {
				j := i - layout.digestStart
				bs, zs := b.rows[j][pattern].Bytes(), z.rows[j][pattern].Bytes()
				copy(plain[:32], bs[:])
				copy(plain[32:64], zs[:])
			}
			ss := signing.rows[i][pattern].Bytes()
			copy(plain[len(ciphertext)-32:], ss[:])
			rowXOF(false, rows.scope, i, gate, byte(pattern), labels, nil, ciphertext)
			for k := range ciphertext {
				ciphertext[k] ^= plain[k]
			}
			rowXOF(true, rows.scope, i, gate, byte(pattern), labels, ciphertext, tag)
		}
	}
	return rows, bank
}

type gateTotals struct{ b, z, signing scalar }

func addEncoded(t *testing.T, dst *scalar, encoded []byte) {
	t.Helper()
	var value scalar
	if value.SetBytes((*[32]byte)(encoded)) != 0 {
		t.Fatal("authenticated gate row contains a noncanonical scalar")
	}
	dst.Add(&value)
}

// The opener takes only public archive/geometry and the actually granted
// state labels. It has no access to the dealer, its masks or other labels.
func (rows gateRows) openRange(t *testing.T, states map[int]grantedState, start, stop int) gateTotals {
	t.Helper()
	var totals gateTotals
	for i := start; i < stop; i++ {
		gate := rows.layout.gates[i]
		a, okA := states[gate[0]]
		b, okB := states[gate[1]]
		c, okC := states[gate[2]]
		if !okA || !okB || !okC || a.bit > 1 || b.bit > 1 || c.bit != a.bit^b.bit {
			t.Fatalf("missing or inconsistent eligible state for gate %d", i)
		}
		pattern := a.bit*2 + b.bit
		labels := [3]stateLabel{a.label, b.label, c.label}
		width := (rows.layout.offset(i+1) - rows.layout.offset(i)) / 4
		offset := rows.layout.offset(i) + int(pattern)*width
		packet := rows.wire[offset : offset+width]
		ciphertext, tag := packet[:width-32], packet[width-32:]
		var expected [32]byte
		rowXOF(true, rows.scope, i, gate, pattern, labels, ciphertext, expected[:])
		if subtle.ConstantTimeCompare(expected[:], tag) != 1 {
			t.Fatalf("authentication failed for gate %d", i)
		}
		var plain [96]byte
		rowXOF(false, rows.scope, i, gate, pattern, labels, nil, plain[:len(ciphertext)])
		for k := range ciphertext {
			plain[k] ^= ciphertext[k]
		}
		if rows.layout.isDigestGate(i) {
			addEncoded(t, &totals.b, plain[:32])
			addEncoded(t, &totals.z, plain[32:64])
		}
		addEncoded(t, &totals.signing, plain[len(ciphertext)-32:len(ciphertext)])
	}
	return totals
}
