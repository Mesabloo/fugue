---- MODULE AcceptWithSetBinderInGo ----
\* Expect: accepted, all the way to Go. A set-valued `with (y \in e) { B }` compiles through
\* `Pick` (`runtime/tlaplus/sets.go`), the same uniform-random draw a `variable x \in S`
\* initializer already uses -- pick now, unconditionally, and let a later guard reject the
\* draw the ordinary way (the branch fails, the block's scheduler retries and redraws).
\*
\* This used to be a permanent rejection (`E0061`): thesis §7.2.3.1 declines the construct
\* outright, judging it not worth a real constraint-solving search. This project diverges
\* from the thesis here -- OPEN_QUESTIONS.md §9.36 has the reasoning; this fixture used to be
\* `RejectWithSetBinderInGo.tla`.
\*
\* The counterpart fixture, `AcceptMultiBinderWithDesugarsToChain.tla`, still uses only `=`
\* binders -- unrelated to this restriction now, just keeping that fixture's own concern
\* (multi-binder desugaring) isolated from this one (set-binder Go compilation).

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptWithSetBinderInGo {
    process (P = PID) {
    p1: with (y \in {1, 2}) {
          assert(y = 1 \/ y = 2);
        };
        goto Done;
    }
}*)

====
