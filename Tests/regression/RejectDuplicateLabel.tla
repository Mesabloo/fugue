---- MODULE RejectDuplicateLabel ----
\* Expect: rejected, `WellFormednessError.duplicateLabel`. Two different processes reuse the
\* label `p1` -- labels are one flat namespace across the whole algorithm, matching the original
\* PlusCal-to-TLA+ translator (each label becomes its own top-level TLA+ definition, so two
\* processes cannot reuse one name any more than two operators could), even though a `goto p1`
\* in either process could only ever reach its own.

CONSTANTS
    \* @type: Address;
    PID1,
    \* @type: Address;
    PID2

(*--algorithm RejectDuplicateLabel {
    process (P1 = PID1)
        variables x = 0;
    {
    p1: x := 1;
    }

    process (P2 = PID2)
        variables y = 0;
    {
    p1: y := 1;
    }
}*)

====
