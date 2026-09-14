---- MODULE AcceptConflictingAssignAcrossWhileExit ----
\* Expect: accepted. `y` is written inside the `while`'s own labelled body (before `l2`, i.e.
\* within `l1`'s own atomic step) and again by the trailing, unlabelled statement after the
\* `while` -- these are not the same control path. Entering the while's body always crosses
\* into `l2`'s own atomic step (ending `l1`'s step there, via the `goto` `l2` compiles the loop
\* re-entry to), so the only way to reach the trailing write while still in `l1`'s step is the
\* loop condition being false immediately, never having run the body at all.
\*
\* Regression fixture for `CorePlusCal.Statement.checkAssignConflicts`'s `.while` case
\* (`Desugarer/PlusCal.lean`), which used to propagate the body's writes into whatever followed
\* the `while` unconditionally -- correct only when the body has nowhere else to go, wrong here,
\* where it always diverges into `l2` instead. `AcceptWhileLabelledStep.tla` has the same
\* while-with-internal-label-then-trailing-code shape without a variable conflict to catch this.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptConflictingAssignAcrossWhileExit {
    process (P = PID)
        variables x = 3, y = 0;
    {
    l1: while (x > 0) {
            y := 1;
    l2:     x := x - 1;
        };
        y := 2;
    l3: skip;
        goto l1;
    }
}*)

====
