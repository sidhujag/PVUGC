// Package payselector implements the plaintext, single-message signing fixture.
// It assumes the caller has already authenticated the exact payout and released
// only its selected packets. This package has no fork verifier or custody protocol.
package payselector

import (
	"errors"
	"fmt"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/btcec/v2/schnorr"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/consensys/gnark-crypto/ecc/secp256k1/fr"
)

const (
	bitCount    = 256
	PacketCount = bitCount + 9
)

// Identity contains the BIP340 x-only verification key and precommitted nonce.
type Identity struct {
	Key, Nonce [32]byte
}

// All callers derive the same points and ordering from the selector index alone.
// Filler pairs are disjoint odd positive integers and their field negatives.
func packetPoints() [PacketCount][]fr.Element {
	var points [PacketCount][]fr.Element
	power := fr.One()
	for i := 0; i < bitCount; i++ {
		points[i] = []fr.Element{power}
		power.Double(&power)
	}
	points[bitCount] = []fr.Element{{}}
	odd := uint64(3)
	for digit := 1; digit < 9; digit++ {
		for pair := 0; pair < 1<<(digit-1); pair++ {
			value := fr.NewElement(odd)
			var opposite fr.Element
			opposite.Neg(&value)
			points[bitCount+digit] = append(points[bitCount+digit], value, opposite)
			odd += 2
		}
	}
	return points
}

func randomEvenKey() ([32]byte, fr.Element, error) {
	key, err := btcec.NewPrivateKey()
	if err != nil {
		return [32]byte{}, fr.Element{}, err
	}
	defer key.Zero()
	public := key.PubKey().SerializeCompressed()
	var scalar fr.Element
	secret := key.Serialize()
	scalar.SetBytes(secret)
	clear(secret)
	if public[0] == 3 {
		scalar.Neg(&scalar)
	}
	return [32]byte(public[1:]), scalar, nil
}

// ArmFixture samples a fresh one-message identity and all 265 raw packets.
// This centralized test setup sees all plaintexts. A bridge would require a
// separate verified ceremony to arm and erase distributed secret material.
func ArmFixture() (Identity, [PacketCount][]byte, error) {
	var id Identity
	var packets [PacketCount][]byte
	var polynomial [bitCount + 1]fr.Element
	defer clear(polynomial[:])
	var err error
	id.Key, polynomial[bitCount], err = randomEvenKey()
	if err != nil {
		return Identity{}, packets, err
	}
	id.Nonce, polynomial[bitCount-1], err = randomEvenKey()
	if err != nil {
		return Identity{}, packets, err
	}
	for i := range polynomial[:bitCount-1] {
		if _, err = polynomial[i].SetRandom(); err != nil {
			return Identity{}, packets, err
		}
	}
	for j, group := range packetPoints() {
		for _, point := range group {
			value := polynomial[bitCount]
			for i := bitCount - 1; i >= 0; i-- {
				value.Mul(&value, &point).Add(&value, &polynomial[i])
			}
			encoded := value.Bytes()
			packets[j] = append(packets[j], encoded[:]...)
		}
	}
	return id, packets, nil
}

func challenge(id Identity, digest [32]byte) fr.Element {
	hash := chainhash.TaggedHash(chainhash.TagBIP0340Challenge, id.Nonce[:], id.Key[:], digest[:])
	var e fr.Element
	e.SetBytes(hash[:]) // BIP340 reduces the 256-bit hash modulo the group order.
	return e
}

func slotsFor(e fr.Element) []int {
	encoded := e.Bytes()
	var slots []int
	for bit := 0; bit < bitCount; bit++ {
		if encoded[31-bit/8]&(1<<(bit%8)) != 0 {
			slots = append(slots, bit)
		}
	}
	missing := bitCount - len(slots)
	for digit := 0; digit < 9; digit++ {
		if missing&(1<<digit) != 0 {
			slots = append(slots, bitCount+digit)
		}
	}
	return slots
}

// Selected returns the packet indices required for exactly this BIP340 message.
func Selected(id Identity, digest [32]byte) []int {
	return slotsFor(challenge(id, digest))
}

// Signature computes the leading coefficient of the degree <=255 interpolant
// through the selected 256 distinct evaluations. For an honest polynomial
// this is its nonce coefficient plus its key coefficient times the challenge.
func Signature(id Identity, digest [32]byte, opened map[int][]byte) ([64]byte, error) {
	public, err := schnorr.ParsePubKey(id.Key[:])
	if err != nil {
		return [64]byte{}, fmt.Errorf("verification key: %w", err)
	}
	slots := Selected(id, digest)
	if len(opened) != len(slots) {
		return [64]byte{}, errors.New("incorrect number of selector packets")
	}
	schedule := packetPoints()
	var xs, ys []fr.Element
	for _, slot := range slots {
		packet := opened[slot]
		if len(packet) != len(schedule[slot])*fr.Bytes {
			return [64]byte{}, fmt.Errorf("incorrect length for selector %d", slot)
		}
		for j, point := range schedule[slot] {
			var value fr.Element
			if err := value.SetBytesCanonical(packet[j*fr.Bytes : (j+1)*fr.Bytes]); err != nil {
				return [64]byte{}, fmt.Errorf("selector %d contains a noncanonical value: %w", slot, err)
			}
			xs = append(xs, point)
			ys = append(ys, value)
		}
	}
	denominators := make([]fr.Element, len(xs))
	for i := range xs {
		denominators[i] = fr.One()
		for j := range xs {
			if i != j {
				var difference fr.Element
				difference.Sub(&xs[i], &xs[j])
				denominators[i].Mul(&denominators[i], &difference)
			}
		}
	}
	inverses := fr.BatchInvert(denominators)
	var response fr.Element
	for i := range ys {
		var term fr.Element
		term.Mul(&ys[i], &inverses[i])
		response.Add(&response, &term)
	}
	var sig [64]byte
	copy(sig[:32], id.Nonce[:])
	scalar := response.Bytes()
	copy(sig[32:], scalar[:])
	parsed, err := schnorr.ParseSignature(sig[:])
	if err != nil || !parsed.Verify(digest[:], public) {
		return [64]byte{}, errors.New("selector packets did not produce the authorized signature")
	}
	return sig, nil
}
