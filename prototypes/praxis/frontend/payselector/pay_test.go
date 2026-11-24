package payselector

import (
	"bytes"
	"testing"

	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/wire"
)

func TestPayConservesPrincipal(t *testing.T) {
	id, _, err := ArmFixture()
	if err != nil {
		t.Fatal(err)
	}
	base := Pay{
		Reserve: wire.OutPoint{Hash: [32]byte{1}}, Close: wire.OutPoint{Hash: [32]byte{2}},
		ReserveValue: 100_000, CloseValue: 1_000, RecipientValue: 90_000, Fee: 300,
		RecipientScript: []byte{1}, ChangeScript: []byte{2}, FeeChangeScript: []byte{3}, CloseScript: []byte{4},
	}
	tests := []struct {
		name    string
		edit    func(*Pay)
		amounts []int64
		scripts []byte
	}{
		{"partial principal and fee", nil, []int64{90_000, 10_000, 700}, []byte{1, 2, 3}},
		{"full principal", func(p *Pay) { p.RecipientValue = p.ReserveValue; p.ChangeScript = nil },
			[]int64{100_000, 700}, []byte{1, 3}},
		{"fee cap", func(p *Pay) { p.Fee = p.CloseValue; p.FeeChangeScript = nil },
			[]int64{90_000, 10_000}, []byte{1, 2}},
		{"full principal and fee", func(p *Pay) {
			p.RecipientValue = p.ReserveValue
			p.ChangeScript = nil
			p.Fee = p.CloseValue
			p.FeeChangeScript = nil
		},
			[]int64{100_000}, []byte{1}},
		{"zero fee", func(p *Pay) { p.Fee = 0 }, []int64{90_000, 10_000, 1_000}, []byte{1, 2, 3}},
		{"empty marker value", func(p *Pay) { p.Fee = 0; p.CloseValue = 0; p.FeeChangeScript = nil }, []int64{90_000, 10_000}, []byte{1, 2}},
		{"burn exceeds reserve", func(p *Pay) { p.RecipientValue = p.ReserveValue + 1 }, nil, nil},
		{"fee draws reserve", func(p *Pay) { p.Fee = p.CloseValue + 1 }, nil, nil},
		{"negative fee", func(p *Pay) { p.Fee = -1 }, nil, nil},
		{"input total exceeds supply", func(p *Pay) { p.ReserveValue = btcutil.MaxSatoshi }, nil, nil},
		{"missing reserve change", func(p *Pay) { p.ChangeScript = nil }, nil, nil},
		{"missing fee change", func(p *Pay) { p.FeeChangeScript = nil }, nil, nil},
		{"unexpected reserve change", func(p *Pay) { p.RecipientValue = p.ReserveValue }, nil, nil},
		{"unexpected fee change", func(p *Pay) { p.Fee = p.CloseValue }, nil, nil},
		{"empty recipient script", func(p *Pay) { p.RecipientScript = nil }, nil, nil},
		{"empty close script", func(p *Pay) { p.CloseScript = nil }, nil, nil},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			p := base
			if test.edit != nil {
				test.edit(&p)
			}
			s, err := p.spend(id)
			if test.amounts == nil {
				if err == nil {
					t.Fatal("invalid terms accepted")
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if len(s.tx.TxOut) != len(test.amounts) {
				t.Fatalf("output count %d", len(s.tx.TxOut))
			}
			for i, out := range s.tx.TxOut {
				if out.Value != test.amounts[i] || !bytes.Equal(out.PkScript, []byte{test.scripts[i]}) {
					t.Fatalf("unexpected output %d: %d sat, script %x", i, out.Value, out.PkScript)
				}
			}
		})
	}
}
