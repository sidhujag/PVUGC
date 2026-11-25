package guardednonce

import (
	"crypto/sha256"
	"encoding/hex"
	"testing"

	"github.com/btcsuite/btcd/btcec/v2/schnorr"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
)

// Both independently armed ideal releases serve one script-path Pay. This
// test exercises the Bitcoin combiner, without simulating a custody ceremony.
func TestTwoIndependentSignersInOneReserveLeaf(t *testing.T) {
	a, aFirst, aSecond := newFixture(t)
	b, bFirst, bSecond := newFixture(t)
	ka, kb := a.Public().Key, b.Public().Key
	leafScript, err := txscript.NewScriptBuilder().
		AddData(ka[:]).AddOp(txscript.OP_CHECKSIGVERIFY).
		AddData(kb[:]).AddOp(txscript.OP_CHECKSIG).Script()
	if err != nil {
		t.Fatal(err)
	}
	leaf := txscript.NewBaseTapLeaf(leafScript)
	// The BIP341 NUMS internal key keeps this fixture on its sole script leaf.
	nums, err := hex.DecodeString("50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0")
	if err != nil {
		t.Fatal(err)
	}
	internal, err := schnorr.ParsePubKey(nums)
	if err != nil {
		t.Fatal(err)
	}
	root := leaf.TapHash()
	reserveScript, err := txscript.PayToTaprootScript(txscript.ComputeTaprootOutputKey(internal, root[:]))
	if err != nil {
		t.Fatal(err)
	}
	control := txscript.AssembleTaprootScriptTree(leaf).LeafMerkleProofs[0].ToControlBlock(internal)
	controlBytes, err := control.ToBytes()
	if err != nil {
		t.Fatal(err)
	}

	p2wpkh := func(name string) []byte {
		h := sha256.Sum256([]byte(name))
		return append([]byte{0, 20}, h[:20]...)
	}
	reserve := wire.OutPoint{Hash: sha256.Sum256([]byte("two signer reserve")), Index: 1}
	closeOutput := wire.OutPoint{Hash: sha256.Sum256([]byte("winning close")), Index: 0}
	const reserveValue = 100_000_000
	prevouts := txscript.NewMultiPrevOutFetcher(map[wire.OutPoint]*wire.TxOut{
		reserve:     wire.NewTxOut(reserveValue, reserveScript),
		closeOutput: wire.NewTxOut(10_000, p2wpkh("marker")),
	})
	pay := wire.NewMsgTx(2)
	pay.AddTxIn(wire.NewTxIn(&reserve, nil, nil))
	markerIn := wire.NewTxIn(&closeOutput, nil, nil)
	markerIn.Sequence = 100
	pay.AddTxIn(markerIn)
	pay.AddTxOut(wire.NewTxOut(75_000_000, p2wpkh("burn recipient")))
	pay.AddTxOut(wire.NewTxOut(25_000_000, p2wpkh("approved reserve change")))
	pay.AddTxOut(wire.NewTxOut(8_000, p2wpkh("fee contributor")))

	hashes := txscript.NewTxSigHashes(pay, prevouts)
	msg, err := txscript.CalcTapscriptSignaturehash(hashes, txscript.SigHashDefault, pay, 0, prevouts, leaf)
	if err != nil {
		t.Fatal(err)
	}
	m := [32]byte(msg)
	aFirst[m], aSecond[m], bFirst[m], bSecond[m] = true, true, true, true
	var sigs [2][64]byte
	for i, signer := range []*Dealer{a, b} {
		open, err := signer.First(m)
		if err != nil {
			t.Fatal(err)
		}
		sigs[i], err = signer.Second(m, open)
		if err != nil {
			t.Fatal(err)
		}
	}
	// The first CHECKSIGVERIFY consumes the last argument on the initial stack.
	pay.TxIn[0].Witness = wire.TxWitness{sigs[1][:], sigs[0][:], leafScript, controlBytes}
	vm, err := txscript.NewEngine(reserveScript, pay, 0, txscript.StandardVerifyFlags, nil, hashes, reserveValue, prevouts)
	if err != nil {
		t.Fatal(err)
	}
	if err := vm.Execute(); err != nil {
		t.Fatalf("two-signature reserve tapscript: %v", err)
	}
}
