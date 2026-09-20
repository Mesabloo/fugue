---- MODULE RejectMacroArityMismatch ----
\* Expect: rejected, `DesugarError.macroArityMismatch`. `Inc` takes one parameter, called here
\* with two.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroArityMismatch {
    macro Inc(v) {
        v := v + 1;
    }
    process (P = PID)
        variable x = 0;
    {
    p1: Inc(x, 2);
        goto Done;
    }
}*)

====
