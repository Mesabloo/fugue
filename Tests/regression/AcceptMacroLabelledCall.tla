---- MODULE AcceptMacroLabelledCall ----
\* Expect: accepted. A label immediately before a macro call attaches to the call's first
\* expanded statement, matching real PlusCal -- asserted via `goto p2` elsewhere targeting that
\* label, which only resolves if the label survived expansion where it belongs.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroLabelledCall {
    macro Bump(v) {
        v := v + 1;
        print v;
    }
    process (P = PID)
        variable x = 0;
    {
    p1: goto p2;
    p2: Bump(x);
        goto p1;
    }
}*)

====
