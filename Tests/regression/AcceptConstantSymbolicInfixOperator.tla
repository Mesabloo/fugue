---- MODULE AcceptConstantSymbolicInfixOperator ----
\* Expect: accepted. `CONSTANT _@@_` declares an uninterpreted constant under a symbolic infix
\* operator's own name (`@@`, decorative -- no built-in meaning) rather than a plain identifier --
\* `parseOpDecl`'s `"_" InfixOp "_"` production (`Parser_/TLAPlus.lean`).

CONSTANT
    \* @type: (Int, Int) => Int;
    _@@_

====
