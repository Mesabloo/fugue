---- MODULE RejectLabelInMacroBody ----
\* Expect: rejected, `DesugarError.labelInMacroBody`. A label may never appear inside a `macro`
\* body -- direct sibling of `RejectLabelInWith`.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectLabelInMacroBody {
    macro Foo() {
        oops: skip;
    }
    process (P = PID) {
    p1: skip;
        goto Done;
    }
}*)

====
