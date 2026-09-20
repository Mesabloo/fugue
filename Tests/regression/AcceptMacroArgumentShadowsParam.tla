---- MODULE AcceptMacroArgumentShadowsParam ----
\* Expect: accepted. Regression fixture for the substitution-recursion capture landmine: the
\* call site's argument expression (`x + y`) uses an identifier (`x`) equal to the macro's own
\* parameter name. The caller's `x` is a real, unrelated variable and must survive untouched --
\* a buggy fold-of-single-name-substitutions implementation would recurse into the already-
\* spliced argument and keep replacing `x` there, non-terminating on this fixture.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroArgumentShadowsParam {
    macro ShowSum(x) {
        print x;
    }
    process (P = PID)
        variables x = 5, y = 10;
    {
    p1: ShowSum(x + y);
        goto Done;
    }
}*)

====
