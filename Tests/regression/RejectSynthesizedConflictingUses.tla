---- MODULE RejectSynthesizedConflictingUses ----
\* Expect: rejected, E0077. `x` is used both as an `Int` (`x + 1`) and as a `Bool` (the right
\* operand of `/\`); no type is a subtype of both, so its synthesized type has no solution.

EXTENDS Naturals

Bad(x) == x + 1 > 0 /\ x

====
