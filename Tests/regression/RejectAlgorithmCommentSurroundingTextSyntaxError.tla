---- MODULE RejectAlgorithmCommentSurroundingTextSyntaxError ----
\* Expect: rejected. Text before `--algorithm` and after the closing brace does not hide the
\* algorithm: a syntax error inside its body is still reported at its position.

CONSTANTS
    \* @type: Address;
    PID

(* Some random text --algorithm RejectAlgorithmCommentSurroundingTextSyntaxError {
    process (P = PID)
        variables x = 0;
    {
    p1: x := ;
        goto Done;
    }
} some other random text ****)

====
