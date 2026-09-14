---- MODULE AcceptMultiBinderWithDesugarsToChain ----
\* Expect: accepted. A multi-binder `with (x = e1, y = e2, ...) { B }` desugars to a nested
\* chain of single-binder `with`s (`with (x = e1) { with (y = e2) { B } } }`) --
\* `CorePlusCal.Statement.with` only ever binds one variable at a time, by construction
\* (`Core/CorePlusCal/Syntax.lean`'s module doc).
\*
\* Every binder is `=` -- unrelated to whether the Go backend accepts a `\in` binder (it does,
\* `AcceptWithSetBinderInGo.tla`, OPEN_QUESTIONS.md §9.36); this fixture isolates the
\* multi-binder-desugars-to-a-chain concern from that one.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMultiBinderWithDesugarsToChain {
    process (P = PID) {
    p1: with (x = 3, y = 4, z = 5) {
          print x + y + z;
        };
        goto Done;
    }
}*)

====
