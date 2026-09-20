---- MODULE RejectRecursiveOperatorDefinedTwice ----
\* Expect: rejected, `TCError.alreadyDeclared`. `F`'s `RECURSIVE` predeclaration never touches
\* `Γ` (only `Δ`), so the first `F(x) == x` discharges it as usual -- but that puts `F` in `Γ`,
\* and `requireFresh`'s ordinary `f ∉ Γ` premise (`Elaborator/Declarations.lean`'s `.operator`
\* case, unconditional, `RECURSIVE`-discharging or not) then rejects the second definition of the
\* same name exactly as it would for any non-`RECURSIVE` operator defined twice.

RECURSIVE
    \* @type: Int => Int;
    F(_)

F(x) == x
F(x) == x

====
