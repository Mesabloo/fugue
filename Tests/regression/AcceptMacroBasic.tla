---- MODULE AcceptMacroBasic ----
\* Expect: accepted. One `macro`, one param, one call -- the feature's basic case, reaching
\* `.network`/full Go emission.

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptMacroBasic {
    macro Greet(name) {
        print name;
    }
    process (P = PID) {
    p1: Greet("hello");
        goto Done;
    }
}*)

====
