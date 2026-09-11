package tlaplus

import (
	"slices"
	"testing"
)

// TestSetToBag checks the conversion is faithful (one copy per set element)
// and doesn't share a backing array with the Set it came from — Bag[T](s) is
// a type conversion, not a copy, so this is the property that could quietly
// break if a later BagSum/BagDiff ever wrote through a bag in place.
func TestSetToBag(t *testing.T) {
	s := intSet(1, 2, 3)
	b := SetToBag(s)
	if want := intBag(1, 2, 3); !bagsEqual(b, want) {
		t.Errorf("SetToBag(%v) = %v, want %v", s, b, want)
	}
	if got := SetToBag(Set[Int]{}); len(got) != 0 {
		t.Errorf("SetToBag(empty) = %v, want empty", got)
	}
}

// TestBagToSet checks it both dedups and doesn't mutate its input, the two
// properties SetFilter's own tests pin down for the same reason: b may be
// shared with something else built over the same backing array.
func TestBagToSet(t *testing.T) {
	b := intBag(1, 1, 2, 3, 3, 3)
	before := slices.Clone(b)

	got := BagToSet(IntOrd, b)

	if want := intSet(1, 2, 3); !intsEqual(got, want) {
		t.Errorf("BagToSet(%v) = %v, want %v", b, got, want)
	}
	if !bagsEqual(b, before) {
		t.Errorf("BagToSet mutated its input: %v, was %v", b, before)
	}
}

func TestBagIn(t *testing.T) {
	b := intBag(1, 1, 2, 4)
	for _, x := range []int{1, 2, 4} {
		if !BagIn(IntOrd, b, MkInt(x)) {
			t.Errorf("BagIn(%v, %d) = false, want true", b, x)
		}
	}
	for _, x := range []int{0, 3, 5} {
		if BagIn(IntOrd, b, MkInt(x)) {
			t.Errorf("BagIn(%v, %d) = true, want false", b, x)
		}
	}
	if BagIn(IntOrd, Bag[Int]{}, MkInt(1)) {
		t.Errorf("BagIn on the empty bag = true, want false")
	}
}

// TestCopiesIn checks the count at every position of a run, not just its
// presence — a run boundary is exactly where an off-by-one would show up.
func TestCopiesIn(t *testing.T) {
	b := intBag(1, 2, 2, 2, 3)
	cases := map[int]int{1: 1, 2: 3, 3: 1, 4: 0, 0: 0}
	for x, want := range cases {
		if got := CopiesIn(IntOrd, b, MkInt(x)); !eqInt(got, want) {
			t.Errorf("CopiesIn(%d, %v) = %v, want %d", x, b, got, want)
		}
	}
	if got := CopiesIn(IntOrd, Bag[Int]{}, MkInt(1)); !eqInt(got, 0) {
		t.Errorf("CopiesIn on the empty bag = %v, want 0", got)
	}
}

// TestBagSum checks multiplicities add on a shared element, that a
// one-sided element carries through untouched, and that neither operand is
// written through — BagSum shares SetUnion's merge structure, and SetUnion
// has no such test because it never appends the same source position twice;
// BagSum's tie branch does.
func TestBagSum(t *testing.T) {
	b1, b2 := intBag(1, 2, 2), intBag(2, 3)
	before1, before2 := slices.Clone(b1), slices.Clone(b2)

	got := BagSum(IntOrd, b1, b2)

	if want := intBag(1, 2, 2, 2, 3); !bagsEqual(got, want) {
		t.Errorf("BagSum(%v, %v) = %v, want %v", b1, b2, got, want)
	}
	if !bagsEqual(b1, before1) || !bagsEqual(b2, before2) {
		t.Errorf("BagSum mutated an operand: %v, %v", b1, b2)
	}
	if got := BagSum(IntOrd, Bag[Int]{}, intBag(1, 2)); !bagsEqual(got, intBag(1, 2)) {
		t.Errorf("BagSum(empty, %v) = %v, want %v", intBag(1, 2), got, intBag(1, 2))
	}
}

// TestBagDiff hand-checks {1,1,2,3} (-) {1,3,3} = {1,2}: the shared element 1
// drops from 2 copies to 1, the shared element 3 has more copies removed
// than it has and disappears entirely (not a negative count), 2 is
// untouched since it's absent from the right operand, and the right
// operand's own 3 (present twice, not once, in B1) confirms removal isn't
// just "element present" but "how many copies".
func TestBagDiff(t *testing.T) {
	b1, b2 := intBag(1, 1, 2, 3), intBag(1, 3, 3)
	if got, want := BagDiff(IntOrd, b1, b2), intBag(1, 2); !bagsEqual(got, want) {
		t.Errorf("BagDiff(%v, %v) = %v, want %v", b1, b2, got, want)
	}

	// An element only in the right operand contributes nothing, per Bags.tla's
	// own definition (domain restricted to the left operand).
	if got, want := BagDiff(IntOrd, intBag(1), intBag(1, 2)), intBag(); !bagsEqual(got, want) {
		t.Errorf("BagDiff({1}, {1,2}) = %v, want empty", got)
	}

	// An element only in the left operand keeps every copy.
	if got, want := BagDiff(IntOrd, intBag(4, 4), intBag()), intBag(4, 4); !bagsEqual(got, want) {
		t.Errorf("BagDiff({4,4}, {}) = %v, want %v", got, want)
	}
}

// TestBagUnion hand-checks BagUnion({{1,2}, {2,3}}) = {1,2,2,3}: the shared
// element 2 sums across both bags in the set, the same way BagSum's tie
// branch does for a single pair — this is the property that makes folding
// BagSum correct instead of ad hoc.
func TestBagUnion(t *testing.T) {
	bags := MkSet(BagOrd(IntOrd), intBag(1, 2), intBag(2, 3))
	if got, want := BagUnion(IntOrd, bags), intBag(1, 2, 2, 3); !bagsEqual(got, want) {
		t.Errorf("BagUnion(%v) = %v, want %v", bags, got, want)
	}
	if got := BagUnion(IntOrd, Set[Bag[Int]]{}); len(got) != 0 {
		t.Errorf("BagUnion(empty set of bags) = %v, want empty", got)
	}
}

// TestBagSqsubseteq checks both the copy-count comparison and the
// domain-subset half of the definition: {1,1,2,3} isn't \sqsubseteq {1,2}
// because of 1's count, and {1,2} isn't \sqsubseteq {1} because 2 is
// missing from the right operand entirely (count 0 there).
func TestBagSqsubseteq(t *testing.T) {
	if !BagSqsubseteq(IntOrd, intBag(1, 2), intBag(1, 1, 2, 3)) {
		t.Errorf("{1,2} \\sqsubseteq {1,1,2,3} = false, want true")
	}
	if BagSqsubseteq(IntOrd, intBag(1, 1, 2, 3), intBag(1, 2)) {
		t.Errorf("{1,1,2,3} \\sqsubseteq {1,2} = true, want false")
	}
	if BagSqsubseteq(IntOrd, intBag(1, 2), intBag(1)) {
		t.Errorf("{1,2} \\sqsubseteq {1} = true, want false (2 is missing on the right)")
	}
	if !BagSqsubseteq(IntOrd, Bag[Int]{}, intBag(1, 2)) {
		t.Errorf("the empty bag \\sqsubseteq {1,2} = false, want true")
	}
}

// TestSubBag hand-checks SubBag({1,1,2}): two runs (1, count 2) and (2, count
// 1) give (2+1)*(1+1) = 6 sub-bags, the Cartesian product of "how many of
// each run to keep."
func TestSubBag(t *testing.T) {
	got := SubBag(IntOrd, intBag(1, 1, 2))
	want := MkSet(BagOrd(IntOrd),
		intBag(), intBag(1), intBag(2), intBag(1, 1), intBag(1, 2), intBag(1, 1, 2))
	if !SetEq(BagOrd(IntOrd), got, want) {
		t.Errorf("SubBag({1,1,2}) = %v, want %v", got, want)
	}
}

// TestSubBagEmpty checks the base case: the empty bag's only sub-bag is
// itself, not the empty set of sub-bags.
func TestSubBagEmpty(t *testing.T) {
	got := SubBag(IntOrd, Bag[Int]{})
	if want := MkSet(BagOrd(IntOrd), Bag[Int]{}); !SetEq(BagOrd(IntOrd), got, want) {
		t.Errorf("SubBag(empty) = %v, want {empty}", got)
	}
}

// TestBagEq checks equality is contents-and-multiplicity based, agreeing
// between bags built two different ways, and disagreeing on multiplicity
// alone (same elements, different counts) — the property that distinguishes
// Bag from Set.
func TestBagEq(t *testing.T) {
	// SetToBag({1,2}) has one copy of 1; {1,1,2} has two: must differ.
	if BagEq(IntOrd, intBag(1, 1, 2), SetToBag(intSet(1, 2))) {
		t.Errorf("{1,1,2} = SetToBag({1,2}), want false: different multiplicity of 1")
	}
	if BagEq(IntOrd, intBag(1, 1, 2), intBag(1, 2)) {
		t.Errorf("{1,1,2} = {1,2}, want false: same elements, different multiplicity")
	}
	if !BagEq(IntOrd, intBag(1, 2, 2), intBag(1, 2, 2)) {
		t.Errorf("{1,2,2} = {1,2,2}, want true")
	}
	if !BagEq(IntOrd, Bag[Int]{}, Bag[Int]{}) {
		t.Errorf("the empty bag is not equal to itself")
	}
}

// TestBagOrd checks BagOrd gives a total preorder usable as a Set[Bag[T]]
// element dictionary — SubBag's own result is exactly such a set, so this is
// load-bearing, not incidental.
func TestBagOrd(t *testing.T) {
	o := BagOrd(IntOrd)
	if !o.Eq(intBag(1, 2), intBag(1, 2)) {
		t.Errorf("BagOrd.Eq({1,2}, {1,2}) = false, want true")
	}
	if o.Eq(intBag(1, 2), intBag(1, 2, 2)) {
		t.Errorf("BagOrd.Eq({1,2}, {1,2,2}) = true, want false")
	}
	if !o.Lt(intBag(1), intBag(1, 2)) {
		t.Errorf("BagOrd.Lt({1}, {1,2}) = false, want true (shorter-and-equal-prefix first)")
	}
	if !o.Lt(intBag(1, 2), intBag(2)) {
		t.Errorf("BagOrd.Lt({1,2}, {2}) = false, want true (1 < 2 at the first position)")
	}
}

// TestBagCardinality checks the total copy count, not the distinct-element
// count — the property BagToSet's own dedup would otherwise hide.
func TestBagCardinality(t *testing.T) {
	if got := BagCardinality(intBag(1, 1, 2)); !eqInt(got, 3) {
		t.Errorf("BagCardinality({1,1,2}) = %v, want 3", got)
	}
	if got := BagCardinality(Bag[Int]{}); !eqInt(got, 0) {
		t.Errorf("BagCardinality(empty) = %v, want 0", got)
	}
}

// TestBagOfAll checks multiplicities sum correctly when F is not injective:
// mapping x mod 2 over {1,1,2,3} sends three copies (1, 1, and 3) to image 1
// and one copy (2) to image 0 — not one copy each the way a Set-valued map
// would collapse them.
func TestBagOfAll(t *testing.T) {
	f := func(x Int) Int { return Mod(x, MkInt(2)) }
	got := BagOfAll(IntOrd, intBag(1, 1, 2, 3), f)
	if n := len(Domain(got)); n != 2 {
		t.Fatalf("DOMAIN BagOfAll({1,1,2,3}, x -> x mod 2) has %d elements, want 2", n)
	}
	if c := FnApply(IntOrd, got, MkInt(0)); !eqInt(c, 1) {
		t.Errorf("BagOfAll({1,1,2,3}, x -> x mod 2)[0] = %v, want 1", c)
	}
	if c := FnApply(IntOrd, got, MkInt(1)); !eqInt(c, 3) {
		t.Errorf("BagOfAll({1,1,2,3}, x -> x mod 2)[1] = %v, want 3", c)
	}
}
