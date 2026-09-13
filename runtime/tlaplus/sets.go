package tlaplus

import "slices"

// Set is the representation of TLA+'s Set(t).
//
// Exactly one of elems and pred is nil at any time, never both and never
// neither. elems holds the finite case: sorted ascending by the element
// dictionary's ordering and duplicate-free, as this type has always been.
// pred holds the infinite case: a plain characteristic predicate, with no
// backing slice at all. Which branch a value is in is fixed once, at
// construction — MkSet and the finite-producing operations below build the
// elems branch, Collect and Nat/Int build the pred branch — and nothing here
// inspects one field to decide how to treat the other.
//
// The finite branch keeps every property this type had before the infinite
// one existed: membership by binary search, equality by an elementwise walk,
// CHOOSE's deterministic pick as the first element. The infinite branch buys
// only membership (SetIn) outright, plus whatever the two/three-operand
// combinators below can decide without enumerating it — restricting it
// further (SetFilter) or combining it with a finite operand (SetIntersect,
// SetDifference) stays well defined, because what gets walked is the finite
// side. Nothing that requires enumerating a Set in full is defined on the
// infinite branch: Cardinality, CHOOSE, Pick, SetMap, SetProduct, SetForall,
// SetExists and SetAsFun (functions.go) all panic outright when handed one,
// the same "well-defined subset of TLA+, undefined outside it, panic there"
// choice this file already makes for CHOOSE on the empty set and functions.go
// makes for FnApply outside a function's domain.
//
// A predicate here always denotes a genuinely infinite set — nothing in this
// package builds one from a predicate that could instead be written as a
// finite elems slice. That is what justifies treating a possibly-infinite
// combination of two infinite operands as infinite outright (SetUnion,
// SetIntersect, SetDifference below): it may occasionally be conservative —
// Nat \cap (Int \ Nat) is actually {}, but this type reports it as an
// infinite value and only panics if something later tries to enumerate it —
// but it is never unsound, since it never reports something infinite as
// finite.
//
// Sortedness and dedup are not required by TLA+ — a set has no order — but a
// canonical representative is what makes the finite operations cheap: an
// elementwise walk for equality instead of a double subset test, a binary
// search for membership instead of a scan, the first element for CHOOSE's
// deterministic pick instead of a search for the minimum. It also gives
// deduplication somewhere natural to happen, since sorting brings equal
// elements together.
type Set[T any] struct {
	elems []T
	pred  func(T) bool
}

// MkSet builds a set from elements in arbitrary order, sorting and
// deduplicating them.
//
// This is what a set literal {e1, ..., en} compiles to. A bare composite
// literal will not do: whether two of those expressions denote the same value
// is generally not decidable until they are evaluated, so the literal may
// hold the same element twice and may hold it out of order.
//
// The result's elems is never nil, even for {}: a variadic call with no
// arguments hands this function a nil slice for elems, and elems == nil with
// pred == nil is the one representation Set must never take — nothing marks
// it as either branch. Every other function in this file that builds a finite
// Set relies on being able to tell "empty" from "not yet built" apart, so this
// is guarded once, here, rather than at every read site.
func MkSet[T any](o Ord[T], elems ...T) Set[T] {
	if elems == nil {
		elems = []T{}
	}
	return Set[T]{elems: normalize(o, elems)}
}

// normalize establishes both of the finite branch's invariants — sorted,
// duplicate-free — on a freshly built slice. It sorts in place and must
// therefore only ever be handed a slice its caller owns.
//
// This works over a plain slice rather than a Set: every caller already knows
// it is building the finite branch, so there is nothing left for normalize to
// decide about which branch the result belongs to.
func normalize[T any](o Ord[T], s []T) []T {
	slices.SortFunc(s, o.Cmp)
	return slices.CompactFunc(s, o.Eq)
}

// SetIn reports whether x is an element of s.
//
// On the finite branch this is a binary search on the sorted representation,
// as before predicate sets existed. On the infinite branch it is exactly
// s.pred(x): a predicate set carries no other information, and needs none —
// membership is the one question it exists to answer without enumerating
// anything.
func SetIn[T any](o Ord[T], s Set[T], x T) bool {
	if s.pred != nil {
		return s.pred(x)
	}
	_, found := slices.BinarySearchFunc(s.elems, x, o.Cmp)
	return found
}

// SetEq reports whether two sets have the same elements.
//
// Two finite sets are equal exactly when their sorted representations are
// equal elementwise, so this is a single linear walk rather than a subset
// test in each direction, same as before predicate sets existed.
//
// A finite set is never equal to an infinite one — that much is decidable
// immediately, with no enumeration on either side. Two infinite sets are a
// different matter: deciding whether two arbitrary predicates pick out the
// same values is exactly the undecidable question this type's invariant
// exists to avoid ever requiring, so this panics rather than guessing.
func SetEq[T any](o Ord[T], s, other Set[T]) bool {
	switch {
	case s.pred == nil && other.pred == nil:
		return slices.EqualFunc(s.elems, other.elems, o.Eq)
	case s.pred == nil || other.pred == nil:
		return false
	default:
		panic("Equality of two infinite sets is not implemented")
	}
}

// SetCmp orders two sets lexicographically on their sorted representations
// when both are finite, shorter-and-equal-prefix first.
//
// TLA+ does not order sets, so the direction is arbitrary; it exists so that a
// set can itself be an element of a set, a member of a function's domain, or a
// component of a record. Two finite operands are canonical representatives,
// so this agrees with SetEq: equal sets are equal slices, and so compare
// equal here too.
//
// A finite set sorts before an infinite one — another arbitrary choice, but a
// total and decidable one that needs no enumeration of the infinite side.
// Comparing two infinite sets would need the same undecidable question SetEq
// declines to answer, so it panics for the same reason.
//
// It is three-way rather than a bare SetLt because SetOrd would otherwise walk
// the slices twice to answer Eq and Lt, which compounds at every level of
// nesting.
func SetCmp[T any](o Ord[T], s, other Set[T]) int {
	switch {
	case s.pred == nil && other.pred == nil:
		for i := 0; i < min(len(s.elems), len(other.elems)); i++ {
			if c := o.Cmp(s.elems[i], other.elems[i]); c != 0 {
				return c
			}
		}
		return len(s.elems) - len(other.elems)
	case s.pred == nil:
		return -1
	case other.pred == nil:
		return 1
	default:
		panic("Comparison of infinite sets is not implemented")
	}
}

// SetOrd builds the dictionary for Set[T] from the dictionary for T.
//
// This is what makes Set[Set[Int]] constructible, which the interface-based
// design could not express: SetOrd(SetOrd(IntOrd)) is a dictionary for the
// outer set, composed exactly as the compiler composes the type.
func SetOrd[T any](e Ord[T]) Ord[Set[T]] {
	return Ord[Set[T]]{
		Eq: func(x, y Set[T]) bool { return SetEq(e, x, y) },
		Lt: func(x, y Set[T]) bool { return SetCmp(e, x, y) < 0 },
	}
}

// SetFilter compiles {x \in s : p(x)}.
//
// On the finite branch, removing elements preserves both invariants, so the
// result needs no renormalization. TLA+ values are immutable, so this copies
// before filtering: slices.DeleteFunc compacts in place and would otherwise
// corrupt s, which callers may still hold and which may share a backing array
// with other sets.
//
// On the infinite branch there is no slice to filter, but restricting an
// infinite set further is always well defined without enumerating it: the
// result is simply the conjunction of the two predicates, itself a predicate
// set. This is the one function here that comes out strictly more capable
// once the infinite branch exists, rather than merely safe against it.
func SetFilter[T any](s Set[T], p func(y T) bool) Set[T] {
	if s.pred != nil {
		return Collect(func(x T) bool { return s.pred(x) && p(x) })
	}
	return Set[T]{elems: slices.DeleteFunc(slices.Clone(s.elems), func(y T) bool { return !p(y) })}
}

// SetMap compiles {f(x) : x \in s}.
//
// Neither invariant survives a mapping: f need not be monotone, so the
// results come out in no particular order, and it need not be injective
// either, so {x % 2 : x \in {1, 2, 3}} is two elements from three. Hence the
// dictionary for the result type, and the renormalization.
//
// It panics on an infinite s. Unlike SetFilter, f may relate elements to
// their images in a way no predicate composition can capture, so building the
// output genuinely requires enumerating s, and there is no second operand
// here to enumerate instead.
func SetMap[T, U any](o Ord[U], s Set[T], f func(y T) U) Set[U] {
	if s.pred != nil {
		panic("SetMap of an infinite set")
	}
	out := make([]U, len(s.elems))
	for i, y := range s.elems {
		out[i] = f(y)
	}
	return Set[U]{elems: normalize(o, out)}
}

// SetProduct compiles s \X other, the Cartesian product.
//
// pair cannot build its own result the way SetUnion's elements build
// themselves: a tuple compiles to an anonymous struct only its own
// construction site can name, so pair is taken as a callback, the same way
// SetMap takes its mapping function. When both operands are finite, neither a
// dictionary for U nor a renormalizing pass is needed: pair is always
// injective (distinct (x, y) build distinct tuples, tuple equality being
// componentwise), and row-major order over two sorted, duplicate-free inputs
// is already ascending in a tuple's own lexicographic order — component one
// first, same as the dictionary Network2Go/Ord.lean's ordDict builds for
// Typ.tuple — so both invariants hold by construction.
//
// When one operand is infinite, the product can still be decided without
// touching it if the other operand is a finite, empty set: anything times {}
// is {}, which needs no enumeration of either side. Any other combination
// with an infinite operand panics — pair gives no way to project a result
// element back to the (x, y) that built it, so testing membership in, or
// enumerating, the product would need to enumerate both factors, one of which
// cannot be.
func SetProduct[S, T, U any](s Set[S], other Set[T], pair func(x S, y T) U) Set[U] {
	switch {
	case s.pred == nil && other.pred == nil:
		out := make([]U, 0, len(s.elems)*len(other.elems))
		for _, x := range s.elems {
			for _, y := range other.elems {
				out = append(out, pair(x, y))
			}
		}
		return Set[U]{elems: out}
	case s.pred != nil && other.pred == nil && len(other.elems) == 0:
		return Set[U]{elems: []U{}}
	case other.pred != nil && s.pred == nil && len(s.elems) == 0:
		return Set[U]{elems: []U{}}
	default:
		panic("Cartesian product of an infinite set")
	}
}

// SetUnion compiles s \cup other.
//
// When both operands are finite, this merges the two sorted representations
// in one pass rather than building a result and renormalizing it: the
// operands are sorted and duplicate-free, so the output comes out that way by
// construction, and neither operand is written through.
//
// A union with an infinite operand is always infinite — removing an operand
// from a union only ever shrinks it, never grows it back to finite — so there
// is no demotion to a finite result the way SetIntersect and SetDifference
// below have. The result is a predicate set testing membership in either
// operand via SetIn.
func SetUnion[T any](o Ord[T], s, other Set[T]) Set[T] {
	if s.pred == nil && other.pred == nil {
		out := make([]T, 0, len(s.elems)+len(other.elems))
		i, j := 0, 0
		for i < len(s.elems) && j < len(other.elems) {
			switch c := o.Cmp(s.elems[i], other.elems[j]); {
			case c < 0:
				out = append(out, s.elems[i])
				i++
			case c > 0:
				out = append(out, other.elems[j])
				j++
			default:
				out = append(out, s.elems[i])
				i++
				j++
			}
		}
		out = append(out, s.elems[i:]...)
		out = append(out, other.elems[j:]...)
		return Set[T]{elems: out}
	}
	return Collect(func(x T) bool { return SetIn(o, s, x) || SetIn(o, other, x) })
}

// SetIntersect compiles s \cap other.
//
// When both operands are finite, this merges the two sorted representations
// in one pass, keeping only what both contain, coming out sorted and
// duplicate-free by construction.
//
// Unlike SetUnion, an intersection with one infinite operand can still be
// finite — Nat \cap {1,2,3} certainly is — and deciding it needs only the
// finite operand's elements: enumerate whichever operand is finite and keep
// what the other side's SetIn accepts. That is exactly correct, not a
// heuristic, because the side actually walked is the side that actually is
// finite. Only when both operands are infinite does this fall back to a
// predicate set — conservative, since the true intersection might happen to
// be finite, but sound: it never reports something finite as infinite, only
// ever the reverse.
func SetIntersect[T any](o Ord[T], s, other Set[T]) Set[T] {
	switch {
	case s.pred == nil && other.pred == nil:
		out := make([]T, 0, min(len(s.elems), len(other.elems)))
		i, j := 0, 0
		for i < len(s.elems) && j < len(other.elems) {
			switch c := o.Cmp(s.elems[i], other.elems[j]); {
			case c < 0:
				i++
			case c > 0:
				j++
			default:
				out = append(out, s.elems[i])
				i++
				j++
			}
		}
		return Set[T]{elems: out}
	case s.pred == nil:
		out := make([]T, 0, len(s.elems))
		for _, x := range s.elems {
			if SetIn(o, other, x) {
				out = append(out, x)
			}
		}
		return Set[T]{elems: out}
	case other.pred == nil:
		out := make([]T, 0, len(other.elems))
		for _, x := range other.elems {
			if SetIn(o, s, x) {
				out = append(out, x)
			}
		}
		return Set[T]{elems: out}
	default:
		return Collect(func(x T) bool { return s.pred(x) && other.pred(x) })
	}
}

// SetDifference compiles s \ other.
//
// When both operands are finite, this merges the two sorted representations
// in one pass, keeping what s has and other does not, coming out sorted and
// duplicate-free by construction.
//
// A finite s enumerates itself and filters through other's SetIn regardless
// of whether other is finite or infinite — the same demotion SetIntersect
// makes, and for the same reason: the side actually walked is the side that
// actually is finite. An infinite s with a finite other stays infinite:
// removing finitely many elements from an infinite set cannot make it finite,
// so the result is a predicate set testing s.pred(x) && !SetIn(other, x).
// Two infinite operands also give a predicate set, conservative in the same
// way SetIntersect's both-infinite case is.
func SetDifference[T any](o Ord[T], s, other Set[T]) Set[T] {
	switch {
	case s.pred == nil && other.pred == nil:
		out := make([]T, 0, len(s.elems))
		i, j := 0, 0
		for i < len(s.elems) && j < len(other.elems) {
			switch c := o.Cmp(s.elems[i], other.elems[j]); {
			case c < 0:
				out = append(out, s.elems[i])
				i++
			case c > 0:
				j++
			default:
				i++
				j++
			}
		}
		out = append(out, s.elems[i:]...)
		return Set[T]{elems: out}
	case s.pred == nil:
		out := make([]T, 0, len(s.elems))
		for _, x := range s.elems {
			if !SetIn(o, other, x) {
				out = append(out, x)
			}
		}
		return Set[T]{elems: out}
	case other.pred == nil:
		return Collect(func(x T) bool { return s.pred(x) && !SetIn(o, other, x) })
	default:
		return Collect(func(x T) bool { return s.pred(x) && !other.pred(x) })
	}
}

// SetSubseteq compiles s \subseteq other.
//
// Deciding this needs every element of s checked against other, so an
// infinite s panics unconditionally: there is no other operand whose
// enumeration could substitute, the same shape as SetMap's reasoning.
//
// A finite s against a finite other walks both sorted representations once
// looking for an element of s that other does not have, rather than doing
// len(s) binary searches. Against an infinite other there is no sorted
// representation to walk in lockstep, so this falls back to calling other's
// SetIn once per element of s — still terminating, since s is finite, just
// without the merge trick.
func SetSubseteq[T any](o Ord[T], s, other Set[T]) bool {
	if s.pred != nil {
		panic("\\subseteq of an infinite set")
	}
	if other.pred == nil {
		j := 0
		for i := 0; i < len(s.elems); i++ {
			for j < len(other.elems) && o.Lt(other.elems[j], s.elems[i]) {
				j++
			}
			if j == len(other.elems) || !o.Eq(other.elems[j], s.elems[i]) {
				return false
			}
		}
		return true
	}
	for _, x := range s.elems {
		if !SetIn(o, other, x) {
			return false
		}
	}
	return true
}

// Cardinality compiles FiniteSets!Cardinality(s). The representation is
// duplicate-free, so on the finite branch the element count is the slice
// length.
//
// It panics on an infinite s. FiniteSets!IsFiniteSet has no counterpart in
// this file either way: nothing here decides finiteness at the type level,
// and Nat/Int (naturals.go) are exactly the case that would need such a
// decision if IsFiniteSet were compiled at all.
func Cardinality[T any](s Set[T]) Int {
	if s.pred != nil {
		panic("Cardinality of an infinite set")
	}
	return MkInt(len(s.elems))
}

// Choose compiles CHOOSE x \in s : p(x).
//
// Hilbert's choice operator is deterministic — (CHOOSE x \in s : p) = (CHOOSE x
// \in s : p) has to hold — so this cannot pick at random. Taking the smallest
// satisfying element makes the result depend only on the set's contents, which
// is required: CHOOSE x \in {1, 2} : p and CHOOSE x \in {2, 1} : p must agree,
// those being the same set. Since the representation is sorted, the smallest
// satisfying element is the first one encountered, so this neither builds the
// filtered set nor searches it for a minimum.
//
// It panics when no element satisfies p, that being an undefined expression
// in TLA+, and it panics on an infinite s outright, before ever consulting p:
// there is no way to search for a smallest satisfying element without
// enumerating, and an infinite set cannot be enumerated.
func Choose[T any](s Set[T], p func(y T) bool) T {
	if s.pred != nil {
		panic("CHOOSE over an infinite set")
	}
	for _, y := range s.elems {
		if p(y) {
			return y
		}
	}
	panic("CHOOSE in an empty set")
}

// Pick returns an element of s chosen uniformly at random.
//
// This is what an `x \in S` variable initializer compiles to. It is not
// CHOOSE: the specification says only that the variable starts at some element
// of S, so nothing may depend on which one, and a deterministic pick would
// hide that by always starting from the same place. Choose above is the
// deterministic operator, and the two must not be confused — repeated calls
// here need not agree.
//
// It panics on the empty set, which has no element to return, and on an
// infinite set, which has no uniform distribution to draw from in finite
// time. A specification whose initializer set can be empty is not rejected
// anywhere upstream, so the first is reachable from a well-formed program;
// Nat/Int (naturals.go) make the second reachable too.
func Pick[T any](s Set[T]) T {
	if s.pred != nil {
		panic("Picking from an infinite set")
	}
	if len(s.elems) == 0 {
		panic("Picking from an empty set")
	}
	return s.elems[ToInt(Rand(MkInt(0), MkInt(len(s.elems))))]
}

// Collect builds a set directly from a membership predicate, with no backing
// slice — the infinite branch of Set's representation.
//
// Every predicate handed to this function must denote a genuinely infinite
// set: nothing here can tell the difference at runtime, and every function
// above that treats a Collect-built value as infinite — panicking where
// enumeration would otherwise be needed — relies on that being true by
// construction rather than checked. NatSet/IntSet (naturals.go) are the
// primitive callers; every other predicate set built in this file (SetFilter's
// infinite branch, SetUnion/SetIntersect/SetDifference's infinite-tagged
// results) composes one of those with more predicates, so the property is
// inherited rather than re-established each time.
func Collect[T any](pred func(T) bool) Set[T] { return Set[T]{pred: pred} }

// SetForall compiles \A x \in s : p(x).
//
// It panics on an infinite s: deciding a universally quantified statement
// needs to actually visit every element, and there is no second operand to
// enumerate instead, the same shape as SetMap's and Choose's reasoning.
func SetForall[T any](s Set[T], p func(y T) bool) bool {
	if s.pred != nil {
		panic("\\A over an infinite set")
	}
	for _, y := range s.elems {
		if !p(y) {
			return false
		}
	}
	return true
}

// SetExists compiles \E x \in s : p(x), the dual of SetForall, restricted to
// a finite s for the same reason.
func SetExists[T any](s Set[T], p func(y T) bool) bool {
	if s.pred != nil {
		panic("\\E over an infinite set")
	}
	for _, y := range s.elems {
		if p(y) {
			return true
		}
	}
	return false
}
