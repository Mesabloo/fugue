---- MODULE AcceptConstantOperatorShaped ----
\* Expect: accepted. `CONSTANT F(_, _)` declares an uninterpreted, operator-shaped constant --
\* the written arity (two `_`s) matches its annotation's own arity, so `checkParamArity`
\* (`Elaborator/Declarations.lean`'s `.constants` case) accepts it.

CONSTANT
    \* @type: (Int, Int) => Int;
    F(_, _)

====
