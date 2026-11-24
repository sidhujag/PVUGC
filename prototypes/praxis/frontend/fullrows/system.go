// Package fullrows interprets the public affine-product BQS recipes emitted by
// the compact SP1 frontend. The caller authenticates the compiler manifest.
package fullrows

import (
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"sort"

	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

const Format = "pvugc-affine-product-bqs-v2"
const digestPrefix = "PVUGC affine-product BQS v2\n"

type manifest struct {
	Format      string `json:"format"`
	Fr          string `json:"fr"`
	Unknowns    int    `json:"unknowns"`
	Constraints int    `json:"constraints"`
	MaxProducts int    `json:"max_products"`
	RecipeBytes int64  `json:"recipe_bytes"`
	Digest      string `json:"digest"`
}

// System includes the authenticated manifest and recipe digests. ManifestHash
// is SHA-256 of the exact manifest file, including its whitespace.
type System struct {
	Unknowns     int
	MaxProducts  int
	Rows         []Row
	Digest       [32]byte
	ManifestHash [32]byte
}

type atom struct{ start, width int }

var oneAtom = atom{-1, 0}

func less(a, b atom) bool { return a.start < b.start || a.start == b.start && a.width < b.width }
func (a atom) valid(n int) bool {
	return a == oneAtom || a.start >= 0 && a.width > 0 && a.width <= 254 && a.start <= n-a.width
}
func (a atom) count(w int) int {
	if a == oneAtom || w == 0 {
		return 1
	}
	return (a.width + w - 1) / w
}
func (a atom) digit(i, w, t int) atom {
	if a == oneAtom || w == 0 {
		return a
	}
	width := min(w, a.width-i*w)
	if t > 0 {
		width = min(t, width)
	}
	return atom{a.start + i*w, width}
}

type operation struct {
	x, y        atom
	width, clip int
	k           *kernel
	scale       fr.Element
}
type Row struct {
	unknowns int
	left     []atom
	ops      []operation
}

func (r Row) Count() int { return len(r.left) }

type parser struct {
	n       int
	kernels map[kernelID]*kernel
	domains domainCache
}
type kernelID struct {
	value   string
	n, w, t int
}
type rawTerm struct {
	c    *big.Int
	x, y atom
}
type edge struct{ x, y atom }

// cover mirrors the deterministic public greedy cover used by the compiler.
// Choosing a different cover changes the indexed factors and the QAP.
func cover(terms []rawTerm, w int) map[atom]bool {
	selected := map[atom]bool{}
	edges := map[edge]bool{}
	for _, tt := range terms {
		if tt.x == oneAtom || tt.y == oneAtom {
			continue
		}
		if tt.x == tt.y {
			selected[tt.x] = true
		} else {
			edges[edge{tt.x, tt.y}] = true
		}
	}
	for e := range edges {
		if selected[e.x] || selected[e.y] {
			delete(edges, e)
		}
	}
	for len(edges) > 0 {
		degree := map[atom]int{}
		for e := range edges {
			degree[e.x]++
			degree[e.y]++
		}
		score := -1
		var best atom
		for a, num := range degree {
			v := num * 65536 / a.count(w)
			if v > score || v == score && less(a, best) {
				score = v
				best = a
			}
		}
		selected[best] = true
		for e := range edges {
			if e.x == best || e.y == best {
				delete(edges, e)
			}
		}
	}
	return selected
}

func array(s json.RawMessage, n int) ([]json.RawMessage, error) {
	var v []json.RawMessage
	if e := json.Unmarshal(s, &v); e != nil || n >= 0 && len(v) != n || len(v) == 0 {
		return nil, errors.New("invalid recipe tuple")
	}
	return v, nil
}
func integer(s json.RawMessage) (*big.Int, error) {
	z, ok := new(big.Int).SetString(string(s), 10)
	if !ok {
		return nil, errors.New("non-integral recipe coefficient")
	}
	return z, nil
}
func small(s json.RawMessage) (int, error) {
	var v int
	err := json.Unmarshal(s, &v)
	return v, err
}
func (p *parser) atomParts(x, y json.RawMessage) (atom, error) {
	i, err := small(x)
	if err != nil {
		return atom{}, err
	}
	n, err := small(y)
	if err != nil {
		return atom{}, err
	}
	a := atom{i, n}
	if !a.valid(p.n) {
		return atom{}, errors.New("out-of-range bit slice")
	}
	return a, nil
}
func (p *parser) parseAtom(s json.RawMessage) (atom, error) {
	v, err := array(s, 2)
	if err != nil {
		return atom{}, err
	}
	return p.atomParts(v[0], v[1])
}
func (p *parser) kernel(c *big.Int, n, w, t int) *kernel {
	key := kernelID{c.String(), n, w, t}
	if k := p.kernels[key]; k != nil {
		return k
	}
	k := newKernel(c, n, w, t, p.domains)
	p.kernels[key] = k
	return k
}

func (p *parser) parse(raw json.RawMessage, scale fr.Element, row *Row, keys map[atom]struct{}, nested bool) error {
	items, err := array(raw, -1)
	if err != nil {
		return err
	}
	var kind string
	if err = json.Unmarshal(items[0], &kind); err != nil {
		return err
	}
	switch kind {
	case "pack":
		if len(items) != 2 || nested {
			return errors.New("invalid nested pack")
		}
		parts, err := array(items[1], -1)
		if err != nil {
			return err
		}
		for _, part := range parts {
			pair, err := array(part, 2)
			if err != nil {
				return err
			}
			m, err := integer(pair[0])
			if err != nil || m.Sign() <= 0 || m.Cmp(fr.Modulus()) >= 0 {
				return errors.New("invalid row pack multiplier")
			}
			var f fr.Element
			f.SetBigInt(m)
			f.Mul(&f, &scale)
			if err = p.parse(pair[1], f, row, keys, true); err != nil {
				return err
			}
		}
	case "plain":
		if len(items) != 2 {
			return errors.New("invalid plain row")
		}
		terms, err := array(items[1], -1)
		if err != nil {
			return err
		}
		for _, term := range terms {
			v, err := array(term, 5)
			if err != nil {
				return err
			}
			c, err := integer(v[0])
			if err != nil {
				return err
			}
			x, err := p.atomParts(v[1], v[2])
			if err != nil {
				return err
			}
			y, err := p.atomParts(v[3], v[4])
			if err != nil {
				return err
			}
			keys[x] = struct{}{}
			row.ops = append(row.ops, operation{x: x, y: y, k: p.kernel(c, 1, 0, 0), scale: scale})
		}
	case "digit":
		if len(items) != 8 {
			return errors.New("invalid digital row")
		}
		w, err := small(items[1])
		if err != nil || w < 1 || w > 64 {
			return errors.New("invalid limb width")
		}
		t, err := small(items[2])
		if err != nil || t < 0 || t > 254 {
			return errors.New("invalid low CRT width")
		}
		source, err := array(items[3], -1)
		if err != nil {
			return err
		}
		terms := make([]rawTerm, 0, len(source))
		for _, entry := range source {
			v, err := array(entry, 3)
			if err != nil {
				return err
			}
			c, err := integer(v[0])
			if err != nil {
				return err
			}
			x, err := p.parseAtom(v[1])
			if err != nil {
				return err
			}
			y, err := p.parseAtom(v[2])
			if err != nil {
				return err
			}
			if less(y, x) {
				return errors.New("source terms must use canonical operand order")
			}
			terms = append(terms, rawTerm{c, x, y})
		}
		chosen := cover(terms, w)
		keys[oneAtom] = struct{}{}
		for _, v := range terms {
			x, y := v.x, v.y
			if x != oneAtom && y != oneAtom && !chosen[x] {
				x, y = y, x
			}
			for i := 0; i < x.count(w); i++ {
				keys[x.digit(i, w, t)] = struct{}{}
			}
			row.ops = append(row.ops, operation{x, y, w, t, p.kernel(v.c, x.count(w)+y.count(w)-1, w, t), scale})
		}
		q0, err := integer(items[4])
		if err != nil {
			return err
		}
		k0, err := integer(items[6])
		if err != nil {
			return err
		}
		pmod := fp.Modulus()
		coef := new(big.Int).Neg(pmod)
		constant := new(big.Int).Mul(coef, q0)
		radix := new(big.Int).Lsh(big.NewInt(1), uint(t))
		if t > 0 {
			constant = centered(constant, radix)
			coef = centered(coef, radix)
			constant.Sub(constant, new(big.Int).Mul(k0, radix))
		} else if k0.Sign() != 0 || string(items[7]) != "null" {
			return errors.New("native row has a carry")
		}
		add := func(c *big.Int, a atom) {
			if c.Sign() != 0 {
				row.ops = append(row.ops, operation{x: oneAtom, y: a, k: p.kernel(c, 1, 0, 0), scale: scale})
			}
		}
		add(constant, oneAtom)
		if string(items[5]) != "null" {
			q, err := p.parseAtom(items[5])
			if err != nil || q == oneAtom {
				return errors.New("invalid quotient slice")
			}
			if t > 0 {
				q.width = min(q.width, t)
			}
			add(coef, q)
		}
		if t > 0 && string(items[7]) != "null" {
			k, err := p.parseAtom(items[7])
			if err != nil || k == oneAtom {
				return errors.New("invalid carry slice")
			}
			add(new(big.Int).Neg(radix), k)
		}
	default:
		return fmt.Errorf("unknown row tag %q", kind)
	}
	return nil
}

func Open(manifestPath, recipePath string) (*System, error) {
	raw, err := os.ReadFile(manifestPath)
	if err != nil {
		return nil, err
	}
	var m manifest
	if err = json.Unmarshal(raw, &m); err != nil {
		return nil, err
	}
	if m.Format != Format || m.Fr != fr.Modulus().String() || m.Unknowns < 1 || m.Constraints < 1 || m.MaxProducts < 1 || m.MaxProducts > 2047 || m.RecipeBytes < 1 || m.RecipeBytes == int64(^uint64(0)>>1) {
		return nil, errors.New("invalid BQS manifest")
	}
	expected, err := hex.DecodeString(m.Digest)
	if err != nil || len(expected) != sha256.Size {
		return nil, errors.New("invalid recipe digest")
	}
	f, err := os.Open(recipePath)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var in io.Reader = f
	if filepath.Ext(recipePath) == ".gz" {
		z, err := gzip.NewReader(f)
		if err != nil {
			return nil, err
		}
		defer z.Close()
		in = z
	}
	return parseRows(raw, m, expected, in)
}

func parseRows(raw []byte, m manifest, expected []byte, in io.Reader) (*System, error) {
	data, err := io.ReadAll(io.LimitReader(in, m.RecipeBytes+1))
	if err != nil {
		return nil, err
	}
	h := sha256.New()
	h.Write([]byte(digestPrefix))
	h.Write(data)
	if int64(len(data)) != m.RecipeBytes || !bytes.Equal(expected, h.Sum(nil)) {
		return nil, errors.New("recipe differs from pinned manifest")
	}
	lines := bytes.Split(bytes.TrimSuffix(data, []byte{'\n'}), []byte{'\n'})
	if len(lines) != m.Constraints {
		return nil, errors.New("recipe row count mismatch")
	}
	s := &System{Unknowns: m.Unknowns, MaxProducts: m.MaxProducts, Rows: make([]Row, len(lines)), ManifestHash: sha256.Sum256(raw)}
	copy(s.Digest[:], expected)
	p := parser{n: m.Unknowns, kernels: map[kernelID]*kernel{}, domains: domainCache{}}
	for i, line := range lines {
		row := &s.Rows[i]
		row.unknowns = m.Unknowns
		keys := map[atom]struct{}{}
		if err := p.parse(line, fr.One(), row, keys, false); err != nil {
			return nil, fmt.Errorf("row %d: %w", i, err)
		}
		if len(keys) == 0 || len(keys) > m.MaxProducts {
			return nil, fmt.Errorf("row %d exceeds factor count", i)
		}
		row.left = make([]atom, 0, len(keys))
		for a := range keys {
			row.left = append(row.left, a)
		}
		sort.Slice(row.left, func(i, j int) bool { return less(row.left[i], row.left[j]) })
	}
	return s, nil
}

func checkBits(n int, w []byte) error {
	if len(w) != n/8+(n%8+7)/8 || n%8 != 0 && w[len(w)-1]>>uint(n%8) != 0 {
		return errors.New("invalid witness length or padding")
	}
	return nil
}
func (s *System) CheckWitness(w []byte) error {
	if err := checkBits(s.Unknowns, w); err != nil {
		return err
	}
	for i, row := range s.Rows {
		l, r, err := row.Evaluate(w)
		if err != nil {
			return err
		}
		var sum, term fr.Element
		for j := range l {
			term.Mul(&l[j], &r[j])
			sum.Add(&sum, &term)
		}
		if !sum.IsZero() {
			return fmt.Errorf("unsatisfied BQS row %d", i)
		}
	}
	return nil
}
