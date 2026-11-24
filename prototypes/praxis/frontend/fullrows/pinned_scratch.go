package fullrows

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"math"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// NewPinnedScratch builds a fixture with a_j fixed by a public row and with
// (1-a_j)*b_jl=0 for each scratch wire. The first len(flags) witness bits
// are the flags, followed by perSlot scratch bits per flag in flag order.
// This exercises actual constrained QAP gates. Receipt-dependent selectors
// would need the authenticated source circuit to compute these flags.
func NewPinnedScratch(flags []bool, perSlot int) (*System, error) {
	if len(flags) == 0 || perSlot < 1 || perSlot >= math.MaxInt || len(flags) > math.MaxInt/(1+perSlot) {
		return nil, errors.New("invalid pinned scratch dimensions")
	}
	var recipe bytes.Buffer
	for j, active := range flags {
		fmt.Fprintf(&recipe, "[\"plain\",[[1,%d,1,-1,0]", j)
		if active {
			recipe.WriteString(",[-1,-1,0,-1,0]")
		}
		recipe.WriteString("]]\n")
		for l := range perSlot {
			b := len(flags) + j*perSlot + l
			fmt.Fprintf(&recipe, "[\"plain\",[[1,%d,1,-1,0],[-1,%d,1,%d,1]]]\n", b, b, j)
		}
	}
	h := sha256.New()
	h.Write([]byte(digestPrefix))
	h.Write(recipe.Bytes())
	digest := h.Sum(nil)
	n := len(flags) * (1 + perSlot)
	m := manifest{Format: Format, Fr: fr.Modulus().String(), Unknowns: n, Constraints: n,
		MaxProducts: 2, RecipeBytes: int64(recipe.Len()), Digest: hex.EncodeToString(digest)}
	raw, err := json.Marshal(m)
	if err != nil {
		return nil, err
	}
	return parseRows(raw, m, digest, &recipe)
}
