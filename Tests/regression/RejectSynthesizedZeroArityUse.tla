---- MODULE RejectSynthesizedZeroArityUse ----
\* Expect: rejected, E0026, at the string. `Zero == 0` carries no type annotation; its synthesized
\* type is `Int`, so comparing it with a string fails.

Zero == 0

ASSUME Zero = "a"

====
