---- MODULE AcceptMacroPassByReferenceIndexed ----
\* Expect: accepted. Same `Inc` macro as `AcceptMacroPassByReference`, called as `Inc(arr[k]);` --
\* checks the segment-composition order (the argument's own segments first, then whatever the
\* body appends) rather than just the bare-name case.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroPassByReferenceIndexed {
    macro Inc(v) {
        v := v + 1;
    }
    process (P = PID)
        variables
            arr = [n \in {1, 2} |-> 0],
            k = 1;
    {
    p1: Inc(arr[k]);
        print arr;
    }
}*)

====
