---- MODULE RejectSynthesizedNestedBoundGeneralized ----
\* Expect: rejected, E0026, at the string. `First(s) == Head(s)` carries no type annotation; `s`
\* defaults to its one bound `Seq(?)`, and that inner metavariable generalizes:
\* `First : (Seq(a)) => a`. The result is the element type, so `First(<<1, 2>>)` is an `Int` and
\* cannot be compared with a string.

EXTENDS Sequences

First(s) == Head(s)

ASSUME First(<<1, 2>>) = "a"

====
