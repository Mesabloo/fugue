---- MODULE AcceptRecursiveOperatorGoCodegen ----
\* Expect: accepted, all the way through Go code generation and a real `go build`. `RECURSIVE
\* Even(_), Odd(_)` -- the thesis's own worked example of mutually-recursive operators
\* (`reference/thesis.txt:11186-11214`, Listing 7.2.6, reused near-verbatim here) -- discharges
\* through `Elaborator/Declarations.lean`'s `Δ`-threaded `[Operator definition]` rule (each body
\* checked against `Γ ∪ Δ`, so `Even`'s body sees `Odd` and vice versa, though neither is in `Γ`
\* yet), then compiles through `Network2Go/Definition.lean`'s ordinary parametric-operator path
\* unchanged: two plain Go `func`s, tied together by Go's own order-independent package-level name
\* resolution, no special-casing anywhere for the fact that either is recursive at all.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

RECURSIVE
    \* @type: Int => Bool;
    Even(_),
    \* @type: Int => Bool;
    Odd(_)

Even(n) == CASE n = 0 -> TRUE  [] OTHER -> \lnot Odd(n - 1)
Odd(n)  == CASE n = 0 -> FALSE [] OTHER -> \lnot Even(n - 1)

(*--algorithm AcceptRecursiveOperatorGoCodegen {
    process (P = PID)
        variables
            \* @type: Bool;
            z = FALSE;
    {
    p1: z := Even(4);
        print z;
        goto Done;
    }
}*)

====
