---- MODULE AcceptRecursiveOperatorDefinitionLater ----
\* Expect: accepted. `F`'s defining `==` sits after an unrelated `CONSTANT` declaration rather
\* than immediately following its `RECURSIVE` line -- pins B.1's "a RECURSIVE-declared name's
\* `==` definition may appear anywhere later in the module, not necessarily adjacent." `Δ` has no
\* notion of adjacency at all: it's a plain name-keyed table, read only while checking an operator
\* body, so nothing about its own position in `declarations₁`/`declarations₂` matters.

RECURSIVE
    \* @type: Int => Int;
    F(_)

CONSTANT
    \* @type: Int;
    Unused

F(x) == F(x)

====
