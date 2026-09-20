---- MODULE AcceptMacroCallsMacro ----
\* Expect: accepted. `DoubleAndPrint` calls the already-declared `Double` in its own body -- a
\* non-recursive macro calling another macro, expanded transitively (each call site's body is
\* itself fully expanded before splicing).

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroCallsMacro {
    macro Double(v) {
        v := v * 2;
    }
    macro DoubleAndPrint(v) {
        Double(v);
        print v;
    }
    process (P = PID)
        variable x = 1;
    {
    p1: DoubleAndPrint(x);
        goto Done;
    }
}*)

====
