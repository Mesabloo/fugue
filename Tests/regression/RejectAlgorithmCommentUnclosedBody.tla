---- MODULE RejectAlgorithmCommentUnclosedBody ----
\* Expect: rejected. The comment closes before the algorithm's closing brace: the algorithm ends
\* at `*)`, so its body is reported as unclosed instead of the text after it being lexed.

CONSTANTS
    \* @type: Address;
    PID

(* Some random text --algorithm RejectAlgorithmCommentUnclosedBody {
    process (P = PID)
    {
    p1: skip;
    }
*)

====
