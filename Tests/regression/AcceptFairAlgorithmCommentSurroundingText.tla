---- MODULE AcceptFairAlgorithmCommentSurroundingText ----
\* Expect: accepted. Free-form text may also precede `--fair algorithm` on the same line.

CONSTANTS
    \* @type: Address;
    PID

(* text --fair algorithm AcceptFairAlgorithmCommentSurroundingText {
    process (P = PID)
    {
    p1: skip;
    }
} more text ****)

====
