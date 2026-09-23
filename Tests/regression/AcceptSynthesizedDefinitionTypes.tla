---- MODULE AcceptSynthesizedDefinitionTypes ----
\* Expect: accepted. Operator and function definitions with no `\@type` get their type synthesized
\* from the body. Parameters start as metavariables: one with upper bounds defaults to the tightest
\* (`Inc`, `Twice`, `Pos`), one bounded only by other metavariables merges with them (`Eq`), one
\* left unconstrained becomes a type variable of the resulting scheme (`Id`, `Const`, `Apply`).
\* `Max` joins two metavariable branches through a fresh one. `Sq` is a function definition whose
\* domain comes from `1..3`, and `First` a parameter whose only bound itself contains a
\* metavariable (`Seq(?)`), later generalized.

EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Address;
    PID

Zero == 0
Inc(x) == x + 1
Twice(x) == x + x
Pos(x) == x \in Nat /\ x > 0
Id(x) == x
Const(x, y) == x
Eq(x, y) == x = y
Max(x, y) == IF x > y THEN x ELSE y
Apply(F(_), x) == F(x)
First(s) == Head(s)
Sq[n \in 1..3] == n * n

(*--algorithm AcceptSynthesizedDefinitionTypes {
    process (P = PID) {
    p1: assert Inc(Zero) = 1 /\ Twice(2) = 4 /\ Pos(1);
    p2: assert Id(1) = 1 /\ Id("a") = "a" /\ Const(1, "b") = 1;
    p3: assert Eq(<<1, 2>>, <<1, 2>>) /\ Max(1, 2) = 2 /\ Apply(Inc, 1) = 2;
    p4: assert First(<<3, 4>>) = 3 /\ Sq[2] = 4;
        goto Done;
    }
}*)

====
