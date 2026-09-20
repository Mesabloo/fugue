---- MODULE RejectMacroDuplicateDecl ----
\* Expect: rejected, `DesugarError.duplicateMacroDecl`. Two macros share the name `Foo`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroDuplicateDecl {
    macro Foo() {
        skip;
    }
    macro Foo() {
        skip;
    }
    process (P = PID) {
    p1: skip;
        goto Done;
    }
}*)

====
