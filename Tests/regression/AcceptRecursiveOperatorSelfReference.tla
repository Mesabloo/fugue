---- MODULE AcceptRecursiveOperatorSelfReference ----
\* Expect: accepted. `RECURSIVE F(_)` predeclares `F` into `Δ` (`Elaborator/Declarations.lean`,
\* never into `Γ`); `F`'s own `==` definition then checks its body against `Γ ∪ Δ`, so the
\* self-call in `F(x)`'s own body resolves. No `@type` at the definition site -- `δ`'s own type
\* is used directly (see `AcceptRecursiveOperatorRedundantAnnotationWarns.tla` for the case where
\* one is repeated anyway).

RECURSIVE
    \* @type: Int => Int;
    F(_)

F(x) == F(x)

====
