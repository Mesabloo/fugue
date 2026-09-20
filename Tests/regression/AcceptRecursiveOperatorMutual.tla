---- MODULE AcceptRecursiveOperatorMutual ----
\* Expect: accepted. `Even`/`Odd`-shaped mutual recursion, typecheck-only (see
\* `AcceptRecursiveOperatorGoCodegen.tla` for the same shape compiled and `go build`-checked).
\* Neither definition repeats the `@type` its `RECURSIVE` predeclaration already gave it --
\* `Elaborator/Declarations.lean`'s `.operator` case's `some δτ, none` branch uses `δ`'s type
\* directly, no `requireAnnotation` call. `Even`'s body checks against `Γ ∪ Δ`, so `Odd` (still
\* only in `Δ`, not yet in `Γ`) resolves; `Odd`'s own definition then discharges it in turn.

EXTENDS Naturals

RECURSIVE
    \* @type: Int => Bool;
    Even(_),
    \* @type: Int => Bool;
    Odd(_)

Even(n) == IF n = 0 THEN TRUE ELSE Odd(n - 1)
Odd(n) == IF n = 0 THEN FALSE ELSE Even(n - 1)

====
