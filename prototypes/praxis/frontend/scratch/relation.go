// Package scratch measures honest coordinate recovery on a single native
// research-grid Praxis table. Its small coefficients and ability to call the
// public decoder carry no confidentiality guarantee.
package scratch

import (
	"errors"
	"fmt"
	"io"
	"math/bits"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"pvugc.example/praxis-frontend/fullkem"
	"pvugc.example/praxis-frontend/fullqap"
	"pvugc.example/praxis-frontend/fullrows"
)

// Relation couples the authenticated public BQS rows to the interpolation
// domain and capsule header. The caller pins the expected manifest hash.
type Relation struct {
	rows   *fullrows.System
	domain *fullqap.Domain
	shape  fullkem.Shape
}

func New(system *fullrows.System) (*Relation, error) {
	if system == nil || len(system.Rows) == 0 || system.MaxProducts < 1 {
		return nil, errors.New("missing BQS rows")
	}
	nu := 1 << bits.Len(uint(system.MaxProducts))
	domain, err := fullqap.New(system.Unknowns, len(system.Rows), nu)
	if err != nil {
		return nil, err
	}
	shape := fullkem.Shape{N: domain.N, D: domain.D, Nu: domain.Nu, CosetSize: domain.CosetSize, Statement: system.ManifestHash}
	return &Relation{rows: system, domain: domain, shape: shape}, nil
}

func (r *Relation) WireBytes() (int64, error) {
	return fullkem.WireBytes(r.shape)
}

// Arm writes exactly one public table. Only the setup caller receives the
// coefficients needed to seal its sidecars. The reduced grid samples three
// bits per wire. wireIndices are indexed from zero in the Boolean witness.
func (r *Relation) Arm(dst io.Writer, wireIndices []int) ([]byte, error) {
	return fullkem.EncryptWithScratch(dst, r.shape, func(tau fr.Element) (fullkem.Evaluations, error) {
		q, err := r.domain.Setup(tau, r.rows)
		if errors.Is(err, fullqap.ErrDomainPoint) {
			return fullkem.Evaluations{}, fullkem.ErrDomainPoint
		}
		if err != nil {
			return fullkem.Evaluations{}, err
		}
		return fullkem.Evaluations{A: q.A, B: q.B, FullZ: q.FullZ, Z: q.Z, Z0: q.Z0, Corner: q.Corner}, nil
	}, wireIndices)
}

// Sum constructs the QAP openings for a packed little-endian Boolean witness
// and reads its uniquely determined search sum from the entire public table.
func (r *Relation) Sum(src io.Reader, packedWitness []byte) (int, error) {
	opening, err := r.domain.Open(packedWitness, r.rows)
	if err != nil {
		return 0, err
	}
	witness := make([]bool, r.shape.N)
	for i := range witness {
		witness[i] = packedWitness[i/8]&(1<<uint(i%8)) != 0
	}
	return fullkem.SearchSum(src, r.shape, witness, fullkem.Openings{
		KeyQ: opening.KeyQ, OtherQ: opening.OtherQ, Remainder: opening.Remainder,
	})
}

// Coordinates opens a batch by comparing one baseline sum with one sum per
// legal single-wire toggle. Each Sum call reconstructs the QAP openings, reads
// the whole table, and checks its encodings. A call returns no partial batch.
func (r *Relation) Coordinates(table io.ReadSeeker, baseline []byte, wireIndices []int) ([]byte, error) {
	if len(baseline) != (r.shape.N+7)/8 {
		return nil, errors.New("incorrect baseline length")
	}
	seen := make(map[int]bool, len(wireIndices))
	for _, wire := range wireIndices {
		if wire < 0 || wire >= r.shape.N || seen[wire] {
			return nil, errors.New("invalid or repeated coordinate index")
		}
		if baseline[wire/8]&(1<<uint(wire%8)) != 0 {
			return nil, errors.New("requested scratch coordinate already set in baseline")
		}
		seen[wire] = true
	}
	if _, err := table.Seek(0, io.SeekStart); err != nil {
		return nil, err
	}
	base, err := r.Sum(table, baseline)
	if err != nil {
		return nil, err
	}
	witness := append([]byte(nil), baseline...)
	defer clear(witness)
	values := make([]byte, len(wireIndices))
	for i, wire := range wireIndices {
		bit := byte(1 << uint(wire%8))
		witness[wire/8] |= bit
		if _, err := table.Seek(0, io.SeekStart); err != nil {
			clear(values)
			return nil, err
		}
		sum, err := r.Sum(table, witness)
		witness[wire/8] &^= bit
		if err != nil {
			clear(values)
			return nil, fmt.Errorf("scratch wire %d: %w", wire, err)
		}
		delta := sum - base
		if delta < 2 || delta > 9 {
			clear(values)
			return nil, fmt.Errorf("scratch wire %d outside development profile", wire)
		}
		values[i] = byte(delta)
	}
	return values, nil
}
