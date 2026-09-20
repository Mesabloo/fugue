---- MODULE RejectMacroArgumentNotAssignable ----
\* Expect: rejected, `DesugarError.macroArgumentNotAssignable`. `Inc`'s body writes to its
\* parameter `v`, but the actual argument `3` is not reference-shaped -- nothing to write back
\* to.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroArgumentNotAssignable {
    macro Inc(v) {
        v := v + 1;
    }
    process (P = PID) {
    p1: Inc(3);
        goto Done;
    }
}*)

====
