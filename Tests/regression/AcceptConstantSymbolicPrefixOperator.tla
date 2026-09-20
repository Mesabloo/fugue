---- MODULE AcceptConstantSymbolicPrefixOperator ----
\* Expect: accepted. `CONSTANT -. _` declares an uninterpreted constant under unary minus's own
\* declaration-site spelling -- `-.`, its own atomic lexer token (`Token.«-.»`,
\* `Parser_/Tokens/TLAPlus.lean`), not bare `-` (which would be read as the start of `_-_`'s infix
\* shape, missing its leading `_`).

CONSTANT
    \* @type: Int => Int;
    -. _

====
