package tlaplus

import "slices"

// Bag is the representation of TLA+'s Bags!Bag(t) — a multiset.
//
// The underlying slice carries one invariant the Go type cannot express: it
// is sorted ascending by the element dictionary's ordering. Unlike Set, it is
// not deduplicated — a repeated element is exactly how a Bag records that
// element's multiplicity. Every function here that constructs a Bag is
// responsible for keeping the slice sorted; every function that consumes one
// may rely on it being so.
//
// TLA+ represents a bag as a function into the positive integers (DOMAIN B
// the underlying set, B[e] the copy count); this is a dedicated
// representation instead, coercible to that function view wherever one is
// needed (Elaborator/Subtyping.lean's Bag(τ) <: τ → Int axiom) rather than
// paying a map's overhead for every bag operation. No bag has a runtime
// representation as anything but this type — EmptyBag/SetToBag/(+)/etc. are
// the only way to build one, so unlike Set there is no literal syntax and no
// unsorted-input constructor to normalize.
type Bag[T any] []T

// SetToBag compiles Bags!SetToBag(s), the bag containing one copy of every
// element of s.
//
// A Set is already sorted and duplicate-free, which is a strictly stronger
// invariant than Bag's sorted-with-duplicates-allowed — s already satisfies
// Bag's invariant as-is, so this is a type conversion, not a rebuild.
func SetToBag[T any](s Set[T]) Bag[T] {
	return Bag[T](s)
}

// BagToSet compiles Bags!BagToSet(b), the set of elements at least one copy
// of which is in b.
//
// b is already sorted, so establishing Set's duplicate-free invariant on top
// is a single compaction pass, not a re-sort. Clones before compacting: b may
// share a backing array with another bag (BagSum's unconsumed tail, for
// instance) that the caller still holds, and slices.CompactFunc rewrites in
// place.
func BagToSet[T any](o Ord[T], b Bag[T]) Set[T] {
	return Set[T](slices.CompactFunc(slices.Clone(b), o.Eq))
}

// BagIn compiles Bags!BagIn(e, B) by binary search on the sorted
// representation — duplicates don't affect whether an element is found, only
// how many times.
func BagIn[T any](o Ord[T], b Bag[T], x T) bool {
	_, found := slices.BinarySearchFunc(b, x, o.Cmp)
	return found
}

// CopiesIn compiles Bags!CopiesIn(e, B): the number of copies of e in B, 0 if
// e is not in B at all.
//
// Binary search finds the leftmost occurrence (if any); since b is sorted,
// every other copy of e sits in the contiguous run starting there, so its
// length is the copy count.
func CopiesIn[T any](o Ord[T], b Bag[T], x T) Int {
	i, found := slices.BinarySearchFunc(b, x, o.Cmp)
	if !found {
		return MkInt(0)
	}
	j := i
	for j < len(b) && o.Eq(b[j], x) {
		j++
	}
	return MkInt(j - i)
}

// BagSum compiles Bags!(+), the union of bags b1 and b2 — multiplicities add.
//
// Merges the two sorted representations in one pass, the same technique
// SetUnion uses, except a tie keeps both elements instead of collapsing them
// to one: that is exactly what "multiplicities add" means for a
// sorted-with-duplicates representation. Neither operand is written through.
func BagSum[T any](o Ord[T], b1, b2 Bag[T]) Bag[T] {
	out := make(Bag[T], 0, len(b1)+len(b2))
	i, j := 0, 0
	for i < len(b1) && j < len(b2) {
		switch c := o.Cmp(b1[i], b2[j]); {
		case c < 0:
			out = append(out, b1[i])
			i++
		case c > 0:
			out = append(out, b2[j])
			j++
		default:
			out = append(out, b1[i], b2[j])
			i++
			j++
		}
	}
	out = append(out, b1[i:]...)
	return append(out, b2[j:]...)
}

// BagDiff compiles Bags!(-): b1 with b2's copies removed, one copy per
// matching copy of the same element — an element only in b2 never appears in
// the result, and one only in b1 keeps every one of its copies.
//
// Walks b1 by run (a maximal block of equal elements) rather than element by
// element the way BagSum does: what survives for a shared element depends on
// its two run lengths together, not on pairing individual copies one at a
// time. b2's scan pointer only ever moves forward across iterations, since
// b1's runs are visited in ascending order, so this is one linear pass over
// each operand.
func BagDiff[T any](o Ord[T], b1, b2 Bag[T]) Bag[T] {
	out := make(Bag[T], 0, len(b1))
	j := 0
	for i := 0; i < len(b1); {
		runEnd := i + 1
		for runEnd < len(b1) && o.Eq(b1[runEnd], b1[i]) {
			runEnd++
		}
		count := runEnd - i
		for j < len(b2) && o.Lt(b2[j], b1[i]) {
			j++
		}
		removed := 0
		for j < len(b2) && o.Eq(b2[j], b1[i]) {
			removed++
			j++
		}
		for k := 0; k < count-removed; k++ {
			out = append(out, b1[i])
		}
		i = runEnd
	}
	return out
}

// BagUnion compiles Bags!BagUnion(S), the bag union of every bag in the set
// S.
//
// Multiset sum is associative and commutative, so this is BagSum folded over
// S's elements — no separate algorithm needed.
func BagUnion[T any](o Ord[T], bags Set[Bag[T]]) Bag[T] {
	out := Bag[T]{}
	for _, b := range bags {
		out = BagSum(o, out, b)
	}
	return out
}

// BagSqsubseteq compiles Bags!\sqsubseteq: b2 has at least as many copies of
// every element as b1 does.
//
// One pass over both sorted representations, run by run like BagDiff —
// fails as soon as some element's b1 run outlength its b2 run, including a
// b1 element b2 doesn't have at all (run length 0 there).
func BagSqsubseteq[T any](o Ord[T], b1, b2 Bag[T]) bool {
	j := 0
	for i := 0; i < len(b1); {
		runEnd := i + 1
		for runEnd < len(b1) && o.Eq(b1[runEnd], b1[i]) {
			runEnd++
		}
		count := runEnd - i
		for j < len(b2) && o.Lt(b2[j], b1[i]) {
			j++
		}
		have := 0
		for j < len(b2) && o.Eq(b2[j], b1[i]) {
			have++
			j++
		}
		if have < count {
			return false
		}
		i = runEnd
	}
	return true
}

// SubBag compiles Bags!SubBag(b), the set of every sub-bag of b.
//
// Groups b into (element, count) runs, then builds the Cartesian product of
// "how many copies of this run to keep" (0..count) across runs, processed in
// ascending run order so every combination comes out sorted by construction
// — no separate normalizing pass beyond MkSet's own dedup, which never fires
// here since distinct combinations always differ in at least one run's kept
// count. Exponential in the product of (count+1) across b's distinct
// elements, same character as a real powerset — not a performance bug.
func SubBag[T any](o Ord[T], b Bag[T]) Set[Bag[T]] {
	results := []Bag[T]{{}}
	for i := 0; i < len(b); {
		runEnd := i + 1
		for runEnd < len(b) && o.Eq(b[runEnd], b[i]) {
			runEnd++
		}
		count := runEnd - i
		next := make([]Bag[T], 0, len(results)*(count+1))
		for _, prefix := range results {
			for k := 0; k <= count; k++ {
				combo := slices.Clone(prefix)
				for c := 0; c < k; c++ {
					combo = append(combo, b[i])
				}
				next = append(next, combo)
			}
		}
		results = next
		i = runEnd
	}
	return MkSet(BagOrd(o), results...)
}

// BagEq compiles Bags equality: the same element at the same multiplicity,
// position by position. Sorted-with-duplicates makes this a single
// elementwise walk, the same reasoning as SetEq.
func BagEq[T any](o Ord[T], b, other Bag[T]) bool {
	return slices.EqualFunc(b, other, o.Eq)
}

// BagCmp orders two bags lexicographically on their sorted representations,
// mirroring SetCmp. TLA+ doesn't order bags either; this exists so a bag can
// itself be a set element (SubBag's own result, BagUnion's argument) or
// nest inside a tuple or record.
func BagCmp[T any](o Ord[T], b, other Bag[T]) int {
	for i := 0; i < min(len(b), len(other)); i++ {
		if c := o.Cmp(b[i], other[i]); c != 0 {
			return c
		}
	}
	return len(b) - len(other)
}

// BagOrd builds the dictionary for Bag[T] from the dictionary for T,
// mirroring SetOrd.
func BagOrd[T any](e Ord[T]) Ord[Bag[T]] {
	return Ord[Bag[T]]{
		Eq: func(x, y Bag[T]) bool { return BagEq(e, x, y) },
		Lt: func(x, y Bag[T]) bool { return BagCmp(e, x, y) < 0 },
	}
}
