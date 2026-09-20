---- MODULE RejectRecursiveOperatorAnnotationMismatch ----
\* Expect: rejected, `TCError.recursiveAnnotationMismatch`. `F`'s `RECURSIVE` predeclaration
\* gives it type `(Int) => Int`; its definition's own `@type` disagrees, `(Int) => Str` --
\* `Elaborator/Declarations.lean`'s `.operator` case, the `some δτ, some τ'` branch with
\* `τ' != δτ`.

RECURSIVE
    \* @type: Int => Int;
    F(_)

\* @type: Int => Str;
F(x) == "x"

====
