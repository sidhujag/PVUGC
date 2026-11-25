package guardednonce

import (
	"crypto/sha256"
	"testing"

	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"pvugc.example/praxis-frontend/payselector"
)

// This test seals four legal rows per gate under independent random state
// labels. Selective delivery of the labels is modeled by an ideal grant.
type xorGate [3]int // input p, input q, fresh output p xor q

type xorLayout struct {
	gates       []xorGate
	digestGates []xorGate
	digestStart int
	wires       int
}

func signerLayout() xorLayout {
	layout := xorLayout{wires: 512}
	inputs := make([]int, layout.wires)
	for i := range inputs {
		inputs[i] = i
	}
	var build func([]int)
	build = func(ids []int) {
		if len(ids) == 1 {
			return
		}
		half := len(ids) / 2
		p, q := ids[:half], ids[half:]
		sum := make([]int, half)
		for i := range sum {
			sum[i] = layout.wires
			layout.wires++
			layout.gates = append(layout.gates, xorGate{p[i], q[i], sum[i]})
		}
		start := len(layout.gates)
		build(p)
		if len(ids) == 512 {
			layout.digestStart = start
			layout.digestGates = layout.gates[start:len(layout.gates)]
		}
		build(q)
		build(sum)
	}
	build(inputs)
	return layout
}

func setInput(bits []byte, offset int, data [32]byte) {
	for i := range 256 {
		bits[offset+i] = (data[i/8] >> uint(7-i%8)) & 1
	}
}

// Each source digit is big endian. Walk backward to assign scalar coefficients
// in increasing powers of two and leave non-input coefficients zero.
func placeWeights(weights []scalar, start, width int, unit scalar) {
	for i := start + width - 1; i >= start; i-- {
		weights[i] = unit
		unit.Add(&unit)
	}
}

// Independent samples for every share except the last give the uniform
// distribution on additive shares conditional on the prescribed total.
func takeShare(t *testing.T, remaining *scalar, last bool) scalar {
	t.Helper()
	if last {
		return *remaining
	}
	value, err := randomScalar()
	if err != nil {
		t.Fatal(err)
	}
	var negative scalar
	remaining.Add(negative.NegateVal(&value))
	return value
}

type idealChannel struct {
	rows [][4]scalar
}

func armChannel(t *testing.T, gates []xorGate, wires int, affine [3]scalar, challengeWeight *scalar) idealChannel {
	t.Helper()
	remaining := make([]scalar, wires)
	placeWeights(remaining, 0, 128, affine[1])
	placeWeights(remaining, 128, 128, affine[2])
	if challengeWeight != nil {
		placeWeights(remaining, 256, 256, *challengeWeight)
	}
	last := make([]int, wires)
	for i, gate := range gates {
		for _, w := range gate {
			last[w] = i
		}
	}
	channel := idealChannel{rows: make([][4]scalar, len(gates))}
	constant := affine[0]
	for i, gate := range gates {
		c := takeShare(t, &constant, i+1 == len(gates))
		var slopes [3]scalar
		for j, w := range gate {
			slopes[j] = takeShare(t, &remaining[w], last[w] == i)
		}
		for pattern := range 4 {
			a, b := pattern>>1, pattern&1
			value := c
			for j, bit := range [3]int{a, b, a ^ b} {
				if bit != 0 {
					value.Add(&slopes[j])
				}
			}
			channel.rows[i][pattern] = value
		}
	}
	return channel
}

// Grants contain one state per eligible wire for this particular descriptor.
// Calling grant on the full circuit reuses every matching stage-A grant.
func grant(t *testing.T, gates []xorGate, bits []byte, bank [][2]stateLabel, states map[int]grantedState) {
	t.Helper()
	for _, gate := range gates {
		bits[gate[2]] = bits[gate[0]] ^ bits[gate[1]]
		for _, w := range gate {
			granted := grantedState{bit: bits[w], label: bank[w][bits[w]]}
			if prior, ok := states[w]; ok && prior != granted {
				t.Fatalf("inconsistent state on shared wire %d", w)
			}
			states[w] = granted
		}
	}
}

func TestSharedDigestSubtree(t *testing.T) {
	dealer, first, second := newFixture(t)
	pub := dealer.Public()
	layout := signerLayout()
	if len(layout.gates) != 19_171 || len(layout.digestGates) != 6_305 || 2*layout.wires != 39_366 {
		t.Fatal("unexpected gate or potential wire-state count")
	}
	for i, g := range layout.gates {
		if g[2] != 512+i || g[0] >= g[2] || g[1] >= g[2] || g[0] == g[1] {
			t.Fatal("expected topological order and a fresh ID for each XOR output")
		}
	}
	packets, bank := sealGateRows(t, layout, dealer)
	if len(packets.wire) != 6_521_856 {
		t.Fatalf("unexpected symmetric gate archive size: %d", len(packets.wire))
	}

	id := payselector.Identity{Key: pub.Key}
	pay := payselector.Pay{
		Reserve:      wire.OutPoint{Hash: sha256.Sum256([]byte("shared subtree reserve")), Index: 1},
		ReserveValue: 100_000_000, RecipientValue: 75_000_000, CloseValue: 10_000, Fee: 2_000,
		RecipientScript: []byte{0x51}, ChangeScript: []byte{0x52}, FeeChangeScript: []byte{0x53}, CloseScript: []byte{0x54},
	}
	for _, closeName := range []string{"subtree close A", "subtree close B"} {
		pay.Close = wire.OutPoint{Hash: sha256.Sum256([]byte(closeName))}
		m, err := pay.Digest(id)
		if err != nil {
			t.Fatal(err)
		}
		first[m], second[m] = true, true
		bits := make([]byte, layout.wires)
		states := make(map[int]grantedState, layout.wires)
		setInput(bits, 0, m)
		grant(t, layout.digestGates, bits, bank, states)
		if len(states) != 6_561 {
			t.Fatal("stage A must use only the digest subtree")
		}
		left := packets.openRange(t, states, layout.digestStart, layout.digestStart+len(layout.digestGates))
		open := Opening{B: left.b.Bytes(), Z: left.z.Bytes()}
		reference, err := dealer.First(m)
		if err != nil || open != reference {
			t.Fatal("gate totals differ from the authorized guard opening")
		}
		r, err := pub.Nonce(m, open)
		if err != nil {
			t.Fatal(err)
		}
		hash := chainhash.TaggedHash(chainhash.TagBIP0340Challenge, r.X[:], pub.Key[:], m[:])
		var e scalar
		e.SetBytes((*[32]byte)(hash))
		if r.Odd {
			e.Negate()
		}
		setInput(bits, 256, e.Bytes())
		grant(t, layout.gates, bits, bank, states)
		if len(states) != layout.wires {
			t.Fatal("stage B must reuse the stage-A wire states and cover the entire circuit")
		}
		// The signing contribution in each stage-A row is already visible.
		// Reuse its total here instead of rereading and decrypting those rows.
		root := packets.openRange(t, states, 0, layout.digestStart)
		rest := packets.openRange(t, states, layout.digestStart+len(layout.digestGates), len(layout.gates))
		total := left.signing
		total.Add(&root.signing).Add(&rest.signing)
		if r.Odd {
			total.Negate()
		}
		var sig [64]byte
		copy(sig[:32], r.X[:])
		response := total.Bytes()
		copy(sig[32:], response[:])
		want, err := dealer.Second(m, open)
		if err != nil || sig != want {
			t.Fatal("signing gate total differs from the authorized Bitcoin signature")
		}
		if err := pay.Verify(id, sig); err != nil {
			t.Fatalf("reserve tapscript: %v", err)
		}
	}
	t.Logf("shared wire states=%d, signing gates=%d, guard gates per channel=%d, symmetric row bytes=%d", 2*layout.wires, len(layout.gates), len(layout.digestGates), len(packets.wire))
}
