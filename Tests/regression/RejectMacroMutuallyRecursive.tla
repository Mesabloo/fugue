---- MODULE RejectMacroMutuallyRecursive ----
\* Expect: rejected, `DesugarError.recursiveMacro`. `A` calls `B` calls `A` -- the best single
\* acceptance test that the notes feature actually works end to end: `notePositions` should be
\* the ordered cycle trace, not just a single point.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroMutuallyRecursive {
    macro A() {
        B();
    }
    macro B() {
        A();
    }
    process (P = PID) {
    p1: skip;
        goto Done;
    }
}*)

====
