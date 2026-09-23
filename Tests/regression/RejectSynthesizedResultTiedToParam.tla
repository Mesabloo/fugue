---- MODULE RejectSynthesizedResultTiedToParam ----
\* Expect: rejected, E0026, at the string. `Id(x) == x` carries no type annotation; it generalizes to
\* `(a) => a`, one variable shared by parameter and result. `Id(1)` is therefore an `Int` and cannot
\* be compared with a string. (Generalizing parameter and result separately would accept this.)

Id(x) == x

ASSUME Id(1) = "a"

====
