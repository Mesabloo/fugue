---- MODULE AcceptSymbolicInfixOperatorDefinition ----
\* Expect: accepted. `a !! b == e` defines a fresh infix operator (`!!`, decorative -- no built-in
\* meaning) directly, with no prior `CONSTANT`/`RECURSIVE` predeclaration -- `parseOperator`'s
\* infix shape (`Parser_/TLAPlus.lean`), canonicalized to the same name `!!`'s own *use* sites
\* already desugar to.

\* @type: (Int, Int) => Int;
a !! b == a

\* @type: Int;
X == 1 !! 2

====
