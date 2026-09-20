---- MODULE RejectMacroRecursive ----
\* Expect: rejected, `DesugarError.recursiveMacro`. `Foo` calls itself -- real PlusCal's macros
\* are non-recursive.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroRecursive {
    macro Foo() {
        Foo();
    }
    process (P = PID) {
    p1: skip;
        goto Done;
    }
}*)

====
