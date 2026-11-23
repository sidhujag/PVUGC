package fullrows

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// MinBitsFactoredBuilder.mod([(P//3+19,x,y),(-13,x,x)],[(17,y)],constant=64)
// with x=2^212+37, y=2^154+711, followed by a plain flag*x_low row.
// The expected factor digests below come from Python instantiated_factors.
const fixtureSource = "[[64,[-1,0],[-1,0]],[17,[-1,0],[254,254]],[-13,[0,254],[0,254]],[7296080957279758407415468581752425029565437052432607887563012631548408736213,[0,254],[254,254]],[-1,[-1,0],[508,254]]]"
const fixtureRecipe = "[\"digit\",1,0," + fixtureSource + ",-13535,[762,15],0,null]\n" +
	"[\"pack\",[[1,[\"digit\",1,15," + fixtureSource + ",-13535,[762,15],-13966,[777,15]]],[1073678424,[\"plain\",[[1,792,1,0,9]]]]]]\n"

func TestPublicFactors(t *testing.T) {
	dir := t.TempDir()
	recipePath := filepath.Join(dir, "rows.jsonl")
	manifestPath := filepath.Join(dir, "manifest.json")
	digest := "e0e2ff10d4392fa8931221b54fac98910199ab011892df84d4f8b16f4244b376"
	m := manifest{Format, fr.Modulus().String(), 793, 2, 256, 506, digest}
	metadata, err := json.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	if err = os.WriteFile(manifestPath, metadata, 0600); err != nil {
		t.Fatal(err)
	}
	if err = os.WriteFile(recipePath, []byte(fixtureRecipe), 0600); err != nil {
		t.Fatal(err)
	}
	s, err := Open(manifestPath, recipePath)
	if err != nil {
		t.Fatal(err)
	}
	if s.ManifestHash != sha256.Sum256(metadata) || hex.EncodeToString(s.Digest[:]) != digest {
		t.Fatal("incorrect manifest or recipe digest")
	}
	valid, err := hex.DecodeString("25000000000000000000000000000000000000000000000000001000000000c0b100000000000000000000000000000000000001000000000000000000000060635fd16be0d94cc2efde7d4e2ee8d766663cff30ec461dd22eac63d9045aab7dd35a6f00")
	if err != nil {
		t.Fatal(err)
	}
	if err := s.CheckWitness(valid); err != nil {
		t.Fatal(err)
	}
	checkFactors(t, s, valid, "f1eb585ba4031334bfd1a2a7fd807fe394979a81ea15f619dfbb3d7f59d102ff")
	other := make([]byte, len(valid))
	for i := range other {
		other[i] = byte(73*i + 123)
	}
	other[len(other)-1] &= 1
	checkFactors(t, s, other, "f98801af6b40e9a48f69fd615174a0c70d889108f1e5670cdda0896bc5001e2f")
	if err := s.CheckWitness(other); err == nil {
		t.Fatal("unsatisfied witness accepted")
	}
	valid[len(valid)-1] |= 0x80
	if err := s.CheckWitness(valid); err == nil {
		t.Fatal("noncanonical witness padding accepted")
	}
	if err := os.WriteFile(recipePath, []byte(fixtureRecipe+" "), 0600); err != nil {
		t.Fatal(err)
	}
	if _, err := Open(manifestPath, recipePath); err == nil {
		t.Fatal("unauthenticated recipe accepted")
	}
}

func checkFactors(t *testing.T, s *System, witness []byte, want string) {
	t.Helper()
	hash := sha256.New()
	for _, row := range s.Rows {
		l, r, err := row.Evaluate(witness)
		if err != nil {
			t.Fatal(err)
		}
		lw, rw := make([]fr.Element, len(l)), make([]fr.Element, len(r))
		var wantA, wantB, term fr.Element
		for i := range l {
			lb, rb := l[i].Bytes(), r[i].Bytes()
			hash.Write(lb[:])
			hash.Write(rb[:])
			lw[i].SetUint64(uint64(1 + 17*i))
			rw[i].SetUint64(uint64(31 + 9*i))
			wantA.Add(&wantA, term.Mul(&l[i], &lw[i]))
			wantB.Add(&wantB, term.Mul(&r[i], &rw[i]))
		}
		a, b := make([]fr.Element, s.Unknowns+1), make([]fr.Element, s.Unknowns+1)
		if err := row.AddWeighted(a, b, lw, rw); err != nil {
			t.Fatal(err)
		}
		gotA, gotB := a[0], b[0]
		for j := 0; j < s.Unknowns; j++ {
			if witness[j/8]>>uint(j%8)&1 != 0 {
				gotA.Add(&gotA, &a[j+1])
				gotB.Add(&gotB, &b[j+1])
			}
		}
		if !gotA.Equal(&wantA) || !gotB.Equal(&wantB) {
			t.Fatal("weighted public columns disagree with affine factors")
		}
	}
	if got := fmt.Sprintf("%x", hash.Sum(nil)); got != want {
		t.Fatalf("public factor digest = %s, Python = %s", got, want)
	}
}
