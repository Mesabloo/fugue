---- MODULE RejectOperatorRedeclared ----
\* Expect: rejected, `TCError.alreadyDeclared` (`Elaborator/Declarations.lean`'s `requireFresh`).
\* `X` is defined twice; the second definition would otherwise silently overwrite the first's `Γ`
\* binding with no diagnostic at all.

\* @type: Int;
X == 1

\* @type: Int;
X == 2

====
