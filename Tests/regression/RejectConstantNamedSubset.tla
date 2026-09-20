---- MODULE RejectConstantNamedSubset ----
\* Expect: rejected, `TCError.alreadyDeclared` (`Elaborator/Declarations.lean`'s `requireFresh`).
\* `SUBSET` has no `builtinContext` entry (its typing rule isn't implemented) -- a plain `Γ`-lookup
\* alone would call it free. It's still a permanently reserved TLA+ primitive, caught instead by
\* `requireFresh`'s `reservedNames` list, the same list `RejectSymbolicOperatorCollidesWithIntrinsic`
\* does *not* need, since that one collides with a name `builtinContext` already binds directly.

CONSTANT
    \* @type: Int => Int;
    SUBSET _

====
