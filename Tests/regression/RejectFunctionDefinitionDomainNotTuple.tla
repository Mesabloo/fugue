---- MODULE RejectFunctionDefinitionDomainNotTuple ----
\* Expect: rejected, `TCError.notATupleType` (`Elaborator/Declarations.lean`'s `.function` case,
\* the `_, got => throw (.notATupleType ...)` branch): 2 binders need the annotation's domain to be
\* a 2-element `Typ.tuple`, not the bare `Int` given here.

EXTENDS Naturals

\* @type: Int -> Int;
f[x \in {1, 2}, y \in {1, 2}] == x + y
====
