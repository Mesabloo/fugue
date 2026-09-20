---- MODULE AcceptRecursiveOperatorRedundantAnnotationWarns ----
\* Expect: accepted (with a `redundant-recursive-annotation` warning, suppressible via
\* `-Wno-redundant-recursive-annotation`). `F`'s definition repeats the exact type its
\* `RECURSIVE` predeclaration already gave it -- accepted, but the repetition adds nothing
\* (`Elaborator/Declarations.lean`'s `.operator` case, the `some δτ, some τ'` branch with
\* `τ' == δτ`).

RECURSIVE
    \* @type: Int => Int;
    F(_)

\* @type: Int => Int;
F(x) == x

====
