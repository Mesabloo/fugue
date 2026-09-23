---- MODULE RejectSynthesizedDistinctParamsNotMerged ----
\* Expect: rejected, E0026, at the right-hand string. `Const(x, y) == x` carries no type annotation;
\* it generalizes to `(a, b) => a`: the result is the *first* parameter's type. `Const(1, "b")` is an
\* `Int`, so comparing it with a string fails. (`(a, b) => b` would accept this.)

Const(x, y) == x

ASSUME Const(1, "b") = "b"

====
