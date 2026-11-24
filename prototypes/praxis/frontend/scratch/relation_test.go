package scratch

import (
	"bytes"
	"testing"

	"pvugc.example/praxis-frontend/fullrows"
)

func TestPinnedCoordinateRecovery(t *testing.T) {
	// Wires 0,1,2 are flags. Each of the two active slots has three legal
	// toggle coordinates. Both active slots open against the same bytes.
	system, err := fullrows.NewPinnedScratch([]bool{true, false, true}, 3)
	if err != nil {
		t.Fatal(err)
	}
	relation, err := New(system)
	if err != nil {
		t.Fatal(err)
	}
	wires := []int{3, 4, 5, 9, 10, 11}
	var table bytes.Buffer
	expected, err := relation.Arm(&table, wires)
	if err != nil {
		t.Fatal(err)
	}
	size, err := relation.WireBytes()
	if err != nil || int64(table.Len()) != size {
		t.Fatalf("serialized table size %d, expected %d: %v", table.Len(), size, err)
	}
	baseline := []byte{0b101, 0}
	got, err := relation.Coordinates(bytes.NewReader(table.Bytes()), baseline, wires)
	if err != nil || !bytes.Equal(got, expected) {
		t.Fatalf("honest coordinate equality %t: %v", bytes.Equal(got, expected), err)
	}
	// A different legitimate baseline can already carry an unrelated active
	// scratch wire. The requested three deltas are still exactly the same.
	alternate := append([]byte(nil), baseline...)
	alternate[1] |= 1 << 1
	got, err = relation.Coordinates(bytes.NewReader(table.Bytes()), alternate, wires[:3])
	if err != nil || !bytes.Equal(got, expected[:3]) {
		t.Fatalf("alternate baseline equality %t: %v", bytes.Equal(got, expected[:3]), err)
	}
	if buf, err := relation.Coordinates(bytes.NewReader(table.Bytes()), baseline, []int{3, 6}); err == nil || buf != nil {
		t.Fatal("disabled selector did not reject the whole batch")
	}
	if _, err := relation.Sum(bytes.NewReader(table.Bytes()), []byte{0b111, 0}); err == nil {
		t.Fatal("witness disagrees with public pinned flags")
	}
	if _, err := relation.Coordinates(bytes.NewReader(table.Bytes()), alternate, []int{9}); err == nil {
		t.Fatal("baseline with requested wire already set")
	}
	if _, err := relation.Arm(&table, []int{-1}); err == nil {
		t.Fatal("setup accepted constant column as a scratch wire")
	}
	if _, err := relation.Arm(&table, []int{1, 1}); err == nil {
		t.Fatal("setup accepted repeated wire")
	}
	t.Logf("one serialized table %d bytes; %d wire values recovered", size, len(wires))
}

// BenchmarkOneToggle265 measures both full passes needed for a single fresh
// toggle, including public-point decoding, FFTs and native pairings.
func BenchmarkOneToggle265(b *testing.B) {
	flags := make([]bool, 265)
	baseline := make([]byte, (len(flags)*4+7)/8)
	for i := range flags {
		flags[i] = i%2 == 0
		if flags[i] {
			baseline[i/8] |= 1 << uint(i%8)
		}
	}
	system, err := fullrows.NewPinnedScratch(flags, 3)
	if err != nil {
		b.Fatal(err)
	}
	relation, err := New(system)
	if err != nil {
		b.Fatal(err)
	}
	wires := []int{len(flags)}
	var table bytes.Buffer
	expected, err := relation.Arm(&table, wires)
	if err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	for range b.N {
		got, err := relation.Coordinates(bytes.NewReader(table.Bytes()), baseline, wires)
		if err != nil || !bytes.Equal(got, expected) {
			b.Fatalf("coordinate mismatch: %v", err)
		}
	}
	b.ReportMetric(float64(table.Len()), "table-B")
}
