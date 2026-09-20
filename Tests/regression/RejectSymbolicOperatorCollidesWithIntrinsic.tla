---- MODULE RejectSymbolicOperatorCollidesWithIntrinsic ----
\* Expect: rejected, `TCError.alreadyDeclared` (`Elaborator/Declarations.lean`'s `requireFresh`).
\* `_\in_` names set membership, already bound in `builtinContext`
\* (`Elaborator/Declarations.lean`) directly -- a symbolic `OpDecl` collides with an intrinsic
\* exactly the way a plain-identifier one would, via a plain `Γ`-lookup, no `reservedNames` list
\* needed (contrast `RejectConstantNamedSubset`, which does need it).

CONSTANT
    \* @type: (Int, Int) => Int;
    _\in_

====
