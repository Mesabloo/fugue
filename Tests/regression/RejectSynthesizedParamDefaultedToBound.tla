---- MODULE RejectSynthesizedParamDefaultedToBound ----
\* Expect: rejected, E0026, at the string argument. `Inc` carries no type annotation; `x + 1` bounds
\* `x` by `Int`, so `x` defaults to `Int` rather than becoming a type variable: `Inc : (Int) => Int`.
\* A string argument must not be accepted.

EXTENDS Naturals

Inc(x) == x + 1

ASSUME Inc("a") = 1

====
