package payselector

import (
	"encoding/hex"
	"errors"
	"fmt"

	"github.com/btcsuite/btcd/btcec/v2/schnorr"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/txscript"
	"github.com/btcsuite/btcd/wire"
)

// Pay models already-authenticated burn terms and live Bitcoin prevouts. Input
// zero is the reserve, input one the winning Close output. The transaction
// uses version 2 and block-relative sequence 100 for Close. If Close confirmed
// at height h, BIP68 permits Pay in block h+100. A release requiring 100
// already-mined descendants at evaluation time must verify them separately.
type Pay struct {
	Reserve, Close                                              wire.OutPoint
	ReserveValue, CloseValue, RecipientValue, Fee               int64
	RecipientScript, ChangeScript, FeeChangeScript, CloseScript []byte
}

type spend struct {
	tx            *wire.MsgTx
	prevouts      *txscript.MultiPrevOutFetcher
	leaf          txscript.TapLeaf
	control       []byte
	reserveScript []byte
}

func (p Pay) spend(id Identity) (*spend, error) {
	if p.Reserve == p.Close || p.Close.Index != 0 {
		return nil, errors.New("expected distinct reserve and Close:0 outpoints")
	}
	if p.ReserveValue <= 0 || p.ReserveValue > btcutil.MaxSatoshi ||
		p.CloseValue < 0 || p.CloseValue > btcutil.MaxSatoshi-p.ReserveValue ||
		p.RecipientValue <= 0 || p.RecipientValue > p.ReserveValue ||
		p.Fee < 0 || p.Fee > p.CloseValue {
		return nil, errors.New("invalid Pay amounts")
	}
	reserveChange := p.ReserveValue - p.RecipientValue
	feeChange := p.CloseValue - p.Fee
	if len(p.RecipientScript) == 0 || len(p.CloseScript) == 0 ||
		(reserveChange > 0) != (len(p.ChangeScript) > 0) ||
		(feeChange > 0) != (len(p.FeeChangeScript) > 0) {
		return nil, errors.New("inconsistent Pay scripts")
	}
	if _, err := schnorr.ParsePubKey(id.Key[:]); err != nil {
		return nil, fmt.Errorf("invalid reserve key: %w", err)
	}
	leafScript, err := txscript.NewScriptBuilder().AddData(id.Key[:]).AddOp(txscript.OP_CHECKSIG).Script()
	if err != nil {
		return nil, err
	}
	leaf := txscript.NewBaseTapLeaf(leafScript)
	// The fixed BIP341 NUMS point H is the internal key for this single-leaf fixture.
	numsBytes, err := hex.DecodeString("50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0")
	if err != nil {
		return nil, err
	}
	internal, err := schnorr.ParsePubKey(numsBytes)
	if err != nil {
		return nil, err
	}
	root := leaf.TapHash()
	outputKey := txscript.ComputeTaprootOutputKey(internal, root[:])
	reserveScript, err := txscript.PayToTaprootScript(outputKey)
	if err != nil {
		return nil, err
	}
	proof := txscript.AssembleTaprootScriptTree(leaf).LeafMerkleProofs[0]
	block := proof.ToControlBlock(internal)
	control, err := block.ToBytes()
	if err != nil {
		return nil, err
	}
	tx := wire.NewMsgTx(2)
	tx.AddTxIn(wire.NewTxIn(&p.Reserve, nil, nil))
	closeInput := wire.NewTxIn(&p.Close, nil, nil)
	closeInput.Sequence = 100
	tx.AddTxIn(closeInput)
	// The burn recipient is paid solely from the reserve. Any remaining
	// reserve principal and any unused fee contribution are distinct outputs.
	tx.AddTxOut(wire.NewTxOut(p.RecipientValue, p.RecipientScript))
	if reserveChange > 0 {
		tx.AddTxOut(wire.NewTxOut(reserveChange, p.ChangeScript))
	}
	if feeChange > 0 {
		tx.AddTxOut(wire.NewTxOut(feeChange, p.FeeChangeScript))
	}
	prevouts := txscript.NewMultiPrevOutFetcher(map[wire.OutPoint]*wire.TxOut{
		p.Reserve: wire.NewTxOut(p.ReserveValue, reserveScript),
		p.Close:   wire.NewTxOut(p.CloseValue, p.CloseScript),
	})
	return &spend{tx: tx, prevouts: prevouts, leaf: leaf, control: control, reserveScript: reserveScript}, nil
}

// Digest calculates BIP341/BIP342 SIGHASH_DEFAULT for the reserve CHECKSIG
// leaf with no annex and no OP_CODESEPARATOR.
func (p Pay) Digest(id Identity) ([32]byte, error) {
	s, err := p.spend(id)
	if err != nil {
		return [32]byte{}, err
	}
	hashes := txscript.NewTxSigHashes(s.tx, s.prevouts)
	digest, err := txscript.CalcTapscriptSignaturehash(hashes, txscript.SigHashDefault, s.tx, 0, s.prevouts, s.leaf)
	if err != nil {
		return [32]byte{}, err
	}
	return [32]byte(digest), nil
}

// Verify runs the reserve input's Taproot witness through btcd's Bitcoin script
// engine. Validation of the separate Close input and chain inclusion are
// independent obligations of the caller.
func (p Pay) Verify(id Identity, sig [64]byte) error {
	s, err := p.spend(id)
	if err != nil {
		return err
	}
	s.tx.TxIn[0].Witness = wire.TxWitness{sig[:], s.leaf.Script, s.control}
	hashes := txscript.NewTxSigHashes(s.tx, s.prevouts)
	engine, err := txscript.NewEngine(s.reserveScript, s.tx, 0, txscript.StandardVerifyFlags, nil, hashes, p.ReserveValue, s.prevouts)
	if err != nil {
		return err
	}
	return engine.Execute()
}
