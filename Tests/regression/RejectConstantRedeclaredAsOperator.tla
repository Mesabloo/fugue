---- MODULE RejectConstantRedeclaredAsOperator ----
\* Expect: rejected, `TCError.alreadyDeclared` (`Elaborator/Declarations.lean`'s `requireFresh`).
\* `X` is declared as a `CONSTANT`, then given an operator definition too -- an abstract value and
\* a concrete body for the same name, which `requireFresh` catches generally, not just for a
\* repeated declaration of the same kind.

CONSTANT
    \* @type: Int;
    X

\* @type: Int;
X == 5

====
