---- MODULE RejectSynthesizedInternalUnconstrained ----
\* Expect: rejected, E0043. `{}`'s element type is fixed by nothing, and does not appear in
\* `Size`'s synthesized type `Int`, so it cannot become a type variable of the scheme either.

EXTENDS FiniteSets

Size == Cardinality({})

====
