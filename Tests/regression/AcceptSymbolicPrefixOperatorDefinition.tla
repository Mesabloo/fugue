---- MODULE AcceptSymbolicPrefixOperatorDefinition ----
\* Expect: accepted. `-. x == e` defines unary minus directly, at its own declaration-site
\* spelling (`-.`, `parseOperator`'s prefix shape, `Parser_/TLAPlus.lean`) -- canonicalizing to
\* `PrefixOperator.-`'s own existing name (`"-."`), the same name ordinary `-x` expression syntax
\* already resolves to, so `- N` below reaches this very definition.

\* @type: Int => Int;
-. x == x

CONSTANT
    \* @type: Int;
    N

\* @type: Int;
Y == - N

====
