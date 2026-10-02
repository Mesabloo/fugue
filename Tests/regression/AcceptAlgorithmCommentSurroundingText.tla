---- MODULE AcceptAlgorithmCommentSurroundingText ----
\* Expect: accepted. The algorithm comment holds free-form text before `--algorithm` and after
\* the algorithm's closing brace, including braces, a nested comment, and a run of stars before
\* the closing `*)`.

CONSTANTS
    \* @type: Address;
    PID

(* Some random text { with braces } (* and a nested comment *) here.
--algorithm AcceptAlgorithmCommentSurroundingText {
    process (P = PID)
        variables x = 0, s = {1, 2};
    {
    p1: x := 3;
        goto Done;
    }
}
Some other random text }} { ****)

====
