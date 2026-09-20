---- MODULE RejectMacroUndefined ----
\* Expect: rejected, `DesugarError.undefinedMacro`. `Foo` is never declared as a macro --
\* `Foo(1);` still parses fine (any `Identifier(args)` call-statement does), and fails only once
\* expansion looks it up.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm RejectMacroUndefined {
    process (P = PID) {
    p1: Foo(1);
        goto Done;
    }
}*)

====
