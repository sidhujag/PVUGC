package payselector

import (
	"bytes"
	"testing"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
	"github.com/consensys/gnark-crypto/ecc/secp256k1/fr"
)

func TestSelectorLayout(t *testing.T) {
	points := packetPoints()
	seen := make(map[fr.Element]bool)
	for i, group := range points {
		var sum fr.Element
		for _, x := range group {
			if seen[x] {
				t.Fatalf("duplicate point at slot %d", i)
			}
			seen[x] = true
			sum.Add(&sum, &x)
		}
		if i >= bitCount && !sum.IsZero() {
			t.Fatalf("filler sum for slot %d", i)
		}
	}
	if len(seen) != 767 {
		t.Fatalf("expected 767 evaluation scalars, got %d", len(seen))
	}
	check := func(e fr.Element) {
		slots := slotsFor(e)
		count := 0
		var sum fr.Element
		for _, i := range slots {
			for _, x := range points[i] {
				sum.Add(&sum, &x)
				count++
			}
		}
		if count != bitCount || !sum.Equal(&e) {
			t.Fatalf("count and sum invariant for %x", e.Bytes())
		}
	}
	check(fr.Element{})
	check(fr.One())
	var minusOne fr.Element
	one := fr.One()
	minusOne.Neg(&one)
	check(minusOne)
	// Exercise every attainable filler digit and every single-bit position.
	var bits fr.Element
	for i := 0; i < bitCount; i++ {
		check(points[i][0])
		bits.Add(&bits, &points[i][0])
		check(bits)
	}
}

// This fixture gives the claimant an ordinary single-user key for Close:0.
// Executing both inputs exercises the wire transaction, without implementing
// a shared or conditionally protected Close signer or a chain history.
func TestBothInputsWithClaimantKey(t *testing.T) {
	id, all, err := ArmFixture()
	if err != nil {
		t.Fatal(err)
	}
	claimant, err := btcec.NewPrivateKey()
	if err != nil {
		t.Fatal(err)
	}
	defer claimant.Zero()
	closeScript, err := txscript.PayToTaprootScript(txscript.ComputeTaprootKeyNoScript(claimant.PubKey()))
	if err != nil {
		t.Fatal(err)
	}
	pay := Pay{
		Reserve: wire.OutPoint{Hash: [32]byte{1}, Index: 3}, Close: wire.OutPoint{Hash: [32]byte{2}},
		ReserveValue: 100_000, CloseValue: 1_000, RecipientValue: 100_000, Fee: 500,
		RecipientScript: closeScript, FeeChangeScript: closeScript, CloseScript: closeScript,
	}
	digest, err := pay.Digest(id)
	if err != nil {
		t.Fatal(err)
	}
	opened := map[int][]byte{}
	for _, slot := range Selected(id, digest) {
		opened[slot] = all[slot]
	}
	sig, err := Signature(id, digest, opened)
	if err != nil {
		t.Fatal(err)
	}
	s, err := pay.spend(id)
	if err != nil {
		t.Fatal(err)
	}
	s.tx.TxIn[0].Witness = wire.TxWitness{sig[:], s.leaf.Script, s.control}
	hashes := txscript.NewTxSigHashes(s.tx, s.prevouts)
	s.tx.TxIn[1].Witness, err = txscript.TaprootWitnessSignature(s.tx, hashes, 1, pay.CloseValue, closeScript, txscript.SigHashDefault, claimant)
	if err != nil {
		t.Fatal(err)
	}
	if s.tx.Version != 2 || s.tx.TxIn[1].Sequence != 100 {
		t.Fatal("unexpected relative height-lock encoding")
	}
	for i, input := range s.tx.TxIn {
		prev := s.prevouts.FetchPrevOutput(input.PreviousOutPoint)
		vm, err := txscript.NewEngine(prev.PkScript, s.tx, i, txscript.StandardVerifyFlags, nil, hashes, prev.Value, s.prevouts)
		if err != nil {
			t.Fatal(err)
		}
		if err := vm.Execute(); err != nil {
			t.Fatalf("input %d: %v", i, err)
		}
	}
}

func TestExactPayScriptSpend(t *testing.T) {
	id, all, err := ArmFixture()
	if err != nil {
		t.Fatal(err)
	}
	// Addresses are fixture data. Only the actual reserve witness is executed.
	outputScript := func(tag byte) []byte {
		return append([]byte{txscript.OP_1, txscript.OP_DATA_32}, bytes.Repeat([]byte{tag}, 32)...)
	}
	pay := Pay{
		Reserve:      wire.OutPoint{Hash: [32]byte{1}, Index: 3},
		Close:        wire.OutPoint{Hash: [32]byte{2}, Index: 0},
		ReserveValue: 100_000, CloseValue: 1_000, RecipientValue: 90_000, Fee: 500,
		RecipientScript: outputScript(3), ChangeScript: outputScript(4), CloseScript: outputScript(5), FeeChangeScript: outputScript(6),
	}
	digest, err := pay.Digest(id)
	if err != nil {
		t.Fatal(err)
	}
	slots := Selected(id, digest)
	open := make(map[int][]byte, len(slots))
	totalPlaintext := 0
	for _, slot := range slots {
		open[slot] = all[slot]
		totalPlaintext += len(all[slot])
	}
	if totalPlaintext != 8192 {
		t.Fatalf("selected plaintext size %d", totalPlaintext)
	}
	signature, err := Signature(id, digest, open)
	if err != nil {
		t.Fatal(err)
	}
	if err := pay.Verify(id, signature); err != nil {
		t.Fatal(err)
	}
	repeated, err := Signature(id, digest, open)
	if err != nil || repeated != signature {
		t.Fatalf("same Pay re-open: %v", err)
	}
	for _, change := range []func(*Pay){
		func(p *Pay) { p.Close.Hash[0]++ },
		func(p *Pay) { p.Reserve.Index++ },
		func(p *Pay) { p.RecipientValue++ },
		func(p *Pay) { p.Fee++ },
		func(p *Pay) { p.CloseValue++ },
		func(p *Pay) { p.ReserveValue++ },
		func(p *Pay) { p.RecipientScript = outputScript(6) },
		func(p *Pay) { p.ChangeScript = outputScript(7) },
		func(p *Pay) { p.FeeChangeScript = outputScript(8) },
		func(p *Pay) { p.CloseScript = outputScript(9) },
	} {
		other := pay
		change(&other)
		otherDigest, err := other.Digest(id)
		if err != nil || otherDigest == digest {
			t.Fatalf("changed transaction digest: %v", err)
		}
		if err := other.Verify(id, signature); err == nil {
			t.Fatal("signature accepted for changed Pay")
		}
	}
	first := slots[0]
	delete(open, first)
	if _, err := Signature(id, digest, open); err == nil {
		t.Fatal("missing packet accepted")
	}
	open[first] = bytes.Repeat([]byte{0xff}, len(all[first]))
	if _, err := Signature(id, digest, open); err == nil {
		t.Fatal("noncanonical scalar accepted")
	}
	open[first] = bytes.Clone(all[first])
	open[first][31] ^= 1
	if _, err := Signature(id, digest, open); err == nil {
		t.Fatal("altered packet accepted")
	}
}
