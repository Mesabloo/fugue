---- MODULE RejectSynthesizedRecursiveFunction ----
\* Expect: rejected, E0027. A function definition whose body refers to the function itself needs
\* its `\@type`: the type is needed before the body can be checked.

EXTENDS Naturals

Fact[n \in 0..5] == IF n = 0 THEN 1 ELSE n * Fact[n - 1]

====
