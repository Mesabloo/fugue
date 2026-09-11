---- MODULE AcceptBagAnnotation ----
\* Expect: accepted. `@type: Bag(...)` has no counterpart in Apalache's own annotation language --
\* Bags is represented as `Function(a, Int)` there, which is why this checker used to fake it the
\* same way -- so the parser needs its own production for it (`Parser_/Annotations.lean`), the way
\* `Channel(...)` already is a project-specific extension beyond Apalache. Regression-covers that
\* production existing at all, and parsing a genuinely nested (record) type inside it.

EXTENDS Bags, Naturals

\* @type: Bag({n: Int});
x == SetToBag({[n |-> 1], [n |-> 2]})
====
