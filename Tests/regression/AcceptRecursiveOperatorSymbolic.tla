---- MODULE AcceptRecursiveOperatorSymbolic ----
\* Expect: accepted. `RECURSIVE _+_` -- a symbolic infix `OpDecl` (Part A's `parseOpDecl`, the
\* same combinator `CONSTANT`'s own symbolic forms use) as a `RECURSIVE` predeclaration, self-
\* referenced from its own symbolic definition site (`a + b == ...`). `+` has no builtin meaning
\* here since this module does not `EXTENDS Naturals`/`Integers` -- one of Part A.1's ~40
\* confidently-eligible decorative infix operators.

RECURSIVE
    \* @type: (Int, Int) => Int;
    _+_

a + b == IF a = b THEN a ELSE a + b

====
