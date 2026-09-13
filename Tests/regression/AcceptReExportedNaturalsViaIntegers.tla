---- MODULE AcceptReExportedNaturalsViaIntegers ----
\* Expect: accepted, all the way through Go code generation. The `EXTENDS Integers` surface of the
\* same re-export bug `AcceptReExportedNaturalsViaSequences` covers: `Integers` `EXTENDS Naturals`
\* and declares only `Int` itself, so every arithmetic operator a module gets from `EXTENDS
\* Integers` alone is re-exported, and must stay tagged `Naturals` rather than `Integers`.
\* `Int` itself is not referenced because it plays no part in that re-export question, not because
\* it can't be: `AcceptInfiniteSetsGoCodegen` is where `Int`/`Nat` themselves get exercised.

EXTENDS Integers

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptReExportedNaturalsViaIntegers {
    process (node \in Nodes)
        variables
            \* @type: Int;
            clock = 0;
    {
    p1: await clock < 3;
        clock := clock + 1;
        goto Done;
    }
}*)

====
