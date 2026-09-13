---- MODULE AcceptInfiniteSetsGoCodegen ----
\* Expect: accepted, all the way to Go, and the emitted Go must compile. `Nat`/`Int` used to be
\* rejected outright at `Network2Go/Expression.lean`'s `compileBuiltinVar`, since `Set` had no way to
\* represent an infinite value; they now compile to `tlaplus.NatSet()`/`tlaplus.IntSet()`, backed by
\* `Set`'s predicate branch. Exercises the shapes that unlocks: membership in both (`SetIn`'s
\* predicate branch), a function literal over `Nat` as its domain (previously unreachable, since
\* `LazyFunction.dom` was pinned to the old finite-only `Set`), and `Nat \cap` a finite set, which
\* demotes to a genuinely finite result rather than staying tagged infinite.
\*
\* Also exercises `\A`/`\E` over an ordinary finite set, which no other `goBuild` fixture in this
\* corpus does: `compileQuantifier` used to hand-roll a Go loop indexing the compiled domain
\* directly, which only worked because `Set` used to literally be a Go slice. It now emits a call to
\* the runtime's own `SetForall`/`SetExists`, and this is the one fixture that sends that codegen
\* through a real `go build` rather than only the in-process structural checks.
\*
\* None of this exercises the operators that still panic on an infinite set (`Cardinality`, `CHOOSE`,
\* a quantifier over `Nat` itself, ...) -- those have no representation as a fixture this suite can
\* run, since checking here stops at `go build` succeeding and never executes the emitted binary;
\* the panic paths are covered by `runtime/tlaplus/sets_test.go` instead.

EXTENDS Integers

CONSTANTS
    \* @type: Address;
    PID

\* @type: (Int) => Int;
Sq(i) == i * i

(*--algorithm AcceptInfiniteSetsGoCodegen {
    process (P = PID)
        variables
            \* @type: Bool;
            zeroIsNat = FALSE,
            \* @type: Bool;
            negativeIsInt = FALSE,
            \* @type: Int -> Int;
            squares = [x \in Nat |-> Sq(x)],
            \* @type: Set(Int);
            small = {},
            \* @type: Bool;
            allPositive = FALSE,
            \* @type: Bool;
            someNegative = FALSE;
    {
    p1: zeroIsNat := 0 \in Nat;
        negativeIsInt := -1 \in Int;
        small := Nat \cap {1, 2, 3};
        allPositive := \A x \in {1, 2, 3} : x > 0;
        someNegative := \E x \in {-1, 2, 3} : x < 0;
        assert squares[4] = 16;
        assert small = {1, 2, 3};
        assert allPositive;
        assert someNegative;
        goto Done;
    }
}*)

====
