---- MODULE RejectRecursiveOperatorNeverDefined ----
\* Expect: rejected, `TCError.recursiveNeverDefined` (`Elaborator.lean`'s `Module.check`, checked
\* once both `declarations₁` and `declarations₂` are checked). `F` is predeclared `RECURSIVE` but
\* no `==` definition anywhere in the module discharges it -- `Δ` still holds `F` at the end.

RECURSIVE
    \* @type: Int => Int;
    F(_)

====
