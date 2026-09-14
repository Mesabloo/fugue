---- MODULE AcceptNestedBlockComment ----
\* Expect: accepted. `Parser_/TLAPlus.lean`'s block-comment lexer recurses into itself
\* (`blockComment ... (inner := true)`) so `(* ... (* ... *) ... *)` nests properly rather than
\* the outer comment ending at the first `*)` it sees.

EXTENDS Naturals

\* @type: Bool;
x == TRUE

(* outer (* nested *) comment *)
====
