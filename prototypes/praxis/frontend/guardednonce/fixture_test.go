package guardednonce

import (
	"crypto/sha256"
	"testing"

	"github.com/btcsuite/btcd/btcec/v2/schnorr"
	"github.com/btcsuite/btcd/wire"
	"pvugc.example/praxis-frontend/payselector"
)

func newFixture(t *testing.T) (*Dealer, map[[32]byte]bool, map[[32]byte]bool) {
	t.Helper()
	h, err := SampleH()
	if err != nil {
		t.Fatal(err)
	}
	context := sha256.Sum256([]byte("synthetic regtest reserve input 0"))
	first, second := make(map[[32]byte]bool), make(map[[32]byte]bool)
	allow := func(approved map[[32]byte]bool) Policy {
		return func(scope, digest [32]byte) bool { return scope == context && approved[digest] }
	}
	d, err := NewDealer(context, h, allow(first), allow(second))
	if err != nil {
		t.Fatal(err)
	}
	return d, first, second
}

func TestTwoExactPayoutsAndRepeatedView(t *testing.T) {
	d, first, second := newFixture(t)
	pub := d.Public()
	id := payselector.Identity{Key: pub.Key}
	btcKey, err := schnorr.ParsePubKey(pub.Key[:])
	if err != nil {
		t.Fatal(err)
	}
	pay := payselector.Pay{
		Reserve:      wire.OutPoint{Hash: sha256.Sum256([]byte("reserve")), Index: 1},
		ReserveValue: 100_000_000, RecipientValue: 75_000_000, CloseValue: 10_000, Fee: 2_000,
		RecipientScript: []byte{0x51}, ChangeScript: []byte{0x52}, FeeChangeScript: []byte{0x53}, CloseScript: []byte{0x54},
	}
	var digests [2][32]byte
	var signatures [2][64]byte
	for i, marker := range []string{"first synthetic close", "second synthetic close"} {
		pay.Close = wire.OutPoint{Hash: sha256.Sum256([]byte(marker)), Index: 0}
		m, err := pay.Digest(id)
		if err != nil {
			t.Fatal(err)
		}
		first[m] = true
		open, err := d.First(m)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := pub.Nonce(m, open); err != nil {
			t.Fatal(err)
		}
		if _, err := d.Second(m, open); err == nil {
			t.Fatal("second stage released before its own approval")
		}
		second[m] = true
		sig, err := d.Second(m, open)
		if err != nil {
			t.Fatal(err)
		}
		parsed, err := schnorr.ParseSignature(sig[:])
		if err != nil || !parsed.Verify(m[:], btcKey) {
			t.Fatal("native BIP340 verification failed")
		}
		if err := pay.Verify(id, sig); err != nil {
			t.Fatalf("reserve tapscript: %v", err)
		}
		repeat, err := d.First(m)
		if err != nil || repeat != open {
			t.Fatal("retry changed the guard")
		}
		repeatedSig, err := d.Second(m, repeat)
		if err != nil || repeatedSig != sig {
			t.Fatal("retry changed the Bitcoin signature")
		}
		first[m] = false
		if _, err := d.Second(m, open); err == nil {
			t.Fatal("second stage ignored the source policy on a cached guard opening")
		}
		digests[i], signatures[i] = m, sig
	}
	if digests[0] == digests[1] || signatures[0] == signatures[1] {
		t.Fatal("different close outpoints unexpectedly produced identical results")
	}
}

func TestReversedParityAndGuardChecks(t *testing.T) {
	d, first, second := newFixture(t)
	m := [32]byte{} // Row (1,0,0) isolates the constant coefficient.
	first[m], second[m] = true, true
	d.k[0].SetInt(1).Negate() // U=-G for this synthetic digest, Y is odd.
	c0, finite := encode(add(baseMul(&d.k[0]), mul(&d.b[0], baseMul(&d.x))))
	if !finite {
		t.Fatal("identity coefficient in odd-parity fixture")
	}
	d.setup.C[0] = c0
	open, err := d.First(m)
	if err != nil {
		t.Fatal(err)
	}
	nonce, err := d.Public().Nonce(m, open)
	if err != nil || !nonce.Odd {
		t.Fatal("negative nonce normalization was not exercised")
	}
	sig, err := d.Second(m, open)
	if err != nil {
		t.Fatal(err)
	}
	id, err := schnorr.ParsePubKey(d.setup.Key[:])
	if err != nil {
		t.Fatal(err)
	}
	parsed, err := schnorr.ParseSignature(sig[:])
	if err != nil || !parsed.Verify(m[:], id) {
		t.Fatal("normalized signature did not verify")
	}
	corrupt := open
	corrupt.Z[31] ^= 1
	if _, err := d.Second(m, corrupt); err == nil {
		t.Fatal("corrupt guard opening accepted")
	}
	for i := range corrupt.B {
		corrupt.B[i] = 0xff
	}
	if _, err := d.Public().Nonce(m, corrupt); err == nil {
		t.Fatal("noncanonical guard scalar accepted")
	}
}

func TestDigestHalvesRetainAllBits(t *testing.T) {
	var m [32]byte
	for i := range m {
		m[i] = byte(255 - i)
	}
	halves := digestHalves(m)
	l, r := halves[0].Bytes(), halves[1].Bytes()
	if [16]byte(l[16:]) != [16]byte(m[:16]) || [16]byte(r[16:]) != [16]byte(m[16:]) ||
		[16]byte(l[:16]) != ([16]byte{}) || [16]byte(r[:16]) != ([16]byte{}) {
		t.Fatal("halves were truncated, reversed or reduced")
	}
}
