---- MODULE RejectSynthesizedJoinedBranchesDefaulted ----
\* Expect: rejected, E0026, at the first string argument. `Max` carries no type annotation; its `IF`
\* joins `x` and `y` through a fresh metavariable, and `x > y` bounds both by `Int`, so
\* `Max : (Int, Int) => Int`. String arguments must not be accepted.

EXTENDS Naturals

Max(x, y) == IF x > y THEN x ELSE y

ASSUME Max("a", "b") = "a"

====
