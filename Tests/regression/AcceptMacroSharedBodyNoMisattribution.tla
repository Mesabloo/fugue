---- MODULE AcceptMacroSharedBodyNoMisattribution ----
\* Expect: accepted. One macro, two call sites -- exists to prove that expanding one body at N
\* call sites (which naturally reuses the same in-memory nodes for the literal, unsubstituted
\* parts of the body) doesn't crash or misattribute across expansions, not to assert any specific
\* position.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroSharedBodyNoMisattribution {
    macro Inc(v) {
        v := v + 1;
    }
    process (P = PID)
        variables x = 0, y = 0;
    {
    p1: Inc(x);
        Inc(y);
        goto Done;
    }
}*)

====
