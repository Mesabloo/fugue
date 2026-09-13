package tlaplus

// The Naturals module's operators.
//
// The arithmetic (Add, Sub, Neg, Mul) lives with the Int representation it
// depends on, in int_big.go and int_machine.go. It is exposed as functions
// rather than left to Go's own operators so that the two representations
// present the same surface and generated code is written once, whichever is
// selected.
//
// The comparisons (<, >, =<, >=) are deliberately absent: they compile to the
// derived operations of IntOrd, representation-independent for the same reason.

// IntRange compiles the range operator lo..hi, the set of integers from lo to
// hi inclusive.
//
// The result is empty when hi < lo, matching TLA+. It is built in ascending
// order and cannot repeat, so it satisfies Set's invariants by construction and
// needs no normalization. It is seeded with a real, empty []Int rather than a
// nil one so that an empty range still satisfies elems' never-nil guarantee
// when hi < lo leaves the loop body unreached.
//
// The loop counts with Int rather than a machine integer, so this holds for
// either representation without conversion.
func IntRange(lo, hi Int) Set[Int] {
	out := []Int{}
	one := MkInt(1)
	for i := lo; IntOrd.Le(i, hi); i = Add(i, one) {
		out = append(out, i)
	}
	return Set[Int]{elems: out}
}

// NatSet compiles the builtin set Naturals!Nat: the non-negative integers.
//
// This is the reason Set gained a predicate branch: Nat has no finite
// representation, and TLC-style enumeration of it would simply never
// terminate. Anything that needs to enumerate the result — Cardinality,
// CHOOSE, quantifiers, SetMap, and the rest documented on Set itself — panics
// instead, which is a real improvement over not terminating at all, even
// though it does not admit those operators over Nat.
func NatSet() Set[Int] { return Collect(func(x Int) bool { return IntOrd.Ge(x, MkInt(0)) }) }

// IntSet compiles the builtin set Integers!Int: every integer.
//
// Named IntSet rather than IntInt to avoid colliding with the Int value type
// this package already defines (int_big.go/int_machine.go) — the same
// collision TLA+'s own surface syntax has between the Integers module and its
// Int operator, not something introduced here.
func IntSet() Set[Int] { return Collect(func(Int) bool { return true }) }
