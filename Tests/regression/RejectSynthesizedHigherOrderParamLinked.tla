---- MODULE RejectSynthesizedHigherOrderParamLinked ----
\* Expect: rejected, E0026, at the string argument. `Apply(F(_), x) == F(x)` carries no type
\* annotation; it generalizes to `((a) => b, a) => b`, where `F`'s parameter and `x` share `a`.
\* Passing `Inc : (Int) => Int` bounds `a` by `Int`, so a string for `x` must not be accepted.

EXTENDS Naturals

Inc(x) == x + 1
Apply(F(_), x) == F(x)

ASSUME Apply(Inc, "s") = 1

====
