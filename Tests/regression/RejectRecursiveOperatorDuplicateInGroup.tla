---- MODULE RejectRecursiveOperatorDuplicateInGroup ----
\* Expect: rejected, `TCError.alreadyDeclared`. `F` is named twice within the same `RECURSIVE`
\* list -- caught by `.recursive`'s own `δ.contains x` check (`Elaborator/Declarations.lean`),
\* not by `requireFresh`'s `f ∉ Γ` (neither entry has reached `Γ` yet, only `Δ`) -- the genuinely
\* different branch from `RejectRecursiveOperatorDefinedTwice.tla`, which hits `requireFresh`
\* instead once the first definition has discharged into `Γ`.

RECURSIVE
    \* @type: Int => Int;
    F(_),
    \* @type: Int => Int;
    F(_)

====
