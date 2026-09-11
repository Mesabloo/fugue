---- MODULE AcceptBagAnnotatedEmptyBag ----
\* Expect: accepted. `EmptyBag`'s result type is `Bag(?a)`, a fresh metavariable -- checking it
\* against an explicit `@type: Bag(Int);` annotation needs `subtype`'s `.bag`-vs-`.bag` structural
\* case to recurse into the element type and unify `?a := Int`, the way `.set`/`.seq`/`.tuple`/
\* `.record`/`.operator`/`.function` already do for themselves. Without that case this fell through
\* to `tryAxioms`'s one-directional `Bag(τ) <: τ -> Int` axiom, which cannot succeed here: neither
\* `Bag(?a)` nor `Bag(Int)` is a `Function`. `AcceptEmptyBagPolymorphicReference`/
\* `AcceptEmptyBagUsedTwiceConsistently` only exercise inference through `(+)`'s shared
\* metavariable, never unification against a bare annotation -- this is the shape that broke
\* compiling `Tests/examples/Paxos.tla`'s `votesRcvd = EmptyBag` once it carried a `Bag(...)`
\* annotation of its own.

EXTENDS Bags

\* @type: Bag(Int);
x == EmptyBag
====
