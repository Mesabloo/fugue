---- MODULE AcceptMacroPassByReference ----
\* Expect: accepted. `macro Inc(v) { v := v + 1; }` called as `Inc(counter);` -- a real, common
\* PlusCal idiom: pass a variable by name so the macro can write to it, reaching `.network`/full
\* Go emission with `counter` actually written.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroPassByReference {
    macro Inc(v) {
        v := v + 1;
    }
    process (P = PID)
        variable counter = 0;
    {
    p1: Inc(counter);
        print counter;
    }
}*)

====
