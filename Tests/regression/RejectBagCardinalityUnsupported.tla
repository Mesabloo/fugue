---- MODULE RejectBagCardinalityUnsupported ----
\* Expect: rejected at Go code generation, E0061. `BagCardinality` stays unsupported on purpose --
\* `Sum`-based, and nothing in scope calls it -- pins that the scope boundary actually holds at the
\* Go backend, not just that the operator still typechecks (`Driver/Builtins.lean` gives it a real
\* type either way).

EXTENDS Bags, Naturals

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm RejectBagCardinalityUnsupported {
    process (node \in Nodes)
        variables
            \* @type: Int;
            n = 0;
    {
    p1: n := BagCardinality(SetToBag({1, 2}));
        goto Done;
    }
}*)
====
