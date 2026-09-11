---- MODULE AcceptDomainRecordFieldAccessInBoundedExists ----
\* Expect: accepted. `DOMAIN`'s builtin type is the scheme `(a -> b) => Set(a)`
\* (`Elaborator/Declarations.lean`'s `Γ₀` entry), freshened per use. Applying it to `f` (a
\* plain, concretely-typed function) resolves `a` to f's domain record type via `subtype`'s
\* `_, .mvar b` case during argument-checking -- but that only assigns the metavariable in the
\* ambient `MonadMetavarContext`; the `Typ` tree `DOMAIN f` synthesizes still literally says
\* `.mvar`. `\E m \in DOMAIN f : ...` used to bind `m`'s context type straight from that
\* unresolved-looking `Set(.mvar)`'s element, so `m.val` (record field access on `m`) failed
\* with "Expected a record type, got `?n`" even though `m`'s real type was already known.
\* Regression-covers every `Elaborator/Expressions.lean` rule that infers a domain/callee type
\* and pattern-matches it directly (`.recordAccess`, `indexInto`, `stepInto`, and the
\* `.collect`/`.map'`/`.fn`/`.fnSet`/`.forall`/`.exists`/`.choose` domain-binder rules), now
\* calling `Elaborator/Resolution.lean`'s `instantiateMVars` first.

\* @type: {bal: Int, val: Str} -> Int;
f == [m \in {[bal |-> 0, val |-> "x"]} |-> 1]

\* @type: Bool;
ok == \E m \in DOMAIN f : m.val = "x"
====
