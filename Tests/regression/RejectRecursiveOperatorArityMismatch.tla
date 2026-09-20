---- MODULE RejectRecursiveOperatorArityMismatch ----
\* Expect: rejected, `TCError.paramArityMismatch`. `F(_, _)`'s `OpDecl` declares arity 2, but its
\* `@type` annotation is a 1-argument operator type -- `.recursive`'s own `checkParamArity` call
\* (`Elaborator/Declarations.lean`, the same helper `CONSTANT`'s higher-order parameters and an
\* ordinary operator's own higher-order parameters both already use) rejects the mismatch, no new
\* mechanism needed for `RECURSIVE` specifically.

RECURSIVE
    \* @type: (Int) => Int;
    F(_, _)

====
