---- MODULE RejectSynthesizedCollapsedParamsShareType ----
\* Expect: rejected, E0026, at the string argument. `Eq(x, y) == x = y` carries no type annotation;
\* `x` and `y` are bounded only by the metavariable `=` introduces, so the three merge into one type
\* variable: `Eq : (a, a) => Bool`. Its two arguments must have one type; `1` and `"s"` do not.
\* (Generalizing `x` and `y` separately would accept this.)

Eq(x, y) == x = y

ASSUME Eq(1, "s")

====
