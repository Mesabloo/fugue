module

public import Elaborator.Expressions
public import Core.TypedTLAPlus.Builtins

public section

/-!
  Declaration/module-level checking: `checkDeclaration`/`checkDeclarations`, threading `Γ` (and,
  alongside it, `Δ` — see `Δ`'s own doc comment below) across `CONSTANTS`/`VARIABLES`/`ASSUME`/
  operator-definition/function-definition, plus `builtinContext`, a minimal `Γ₀` prelude of core
  TLA⁺ operators (equality, boolean connectives, core set theory) needed before any user
  declaration is checked.

  Every declaration's expressions are closed out via `resolveMVars` before `checkDeclaration`
  returns, so a metavariable freshened during one declaration doesn't leak unresolved into the
  next declaration's `Γ`.

  `THEOREM` is out of scope: it has no `CoreTLAPlus.Declaration` constructor. `RECURSIVE` is in
  scope (`.recursive`, `Δ`): an operator definition is in scope for its own body, and every
  sibling operator's `Δ`-pending name, exactly while both remain undischarged — self- and
  mutual-recursion, following `reference/thesis.txt:2109-2187` (Fig 3.1.9/3.1.10). An operator
  *not* named by any `RECURSIVE` still gets none of this (`Δ` empty ⟹ no-op), matching the
  pre-`RECURSIVE` behavior below unchanged. Function definitions get self-recursion
  unconditionally (`f` is in scope checking its own body), matching ordinary TLA⁺ recursive
  functions — `Δ` plays no role there, per the thesis's own Function-definition rule.

  A multi-argument function *definition* `f[x₁ ∈ e₁,...,xₙ ∈ eₙ]` isn't pre-tupled the way a
  multi-index *call* is: `n = 1` gives a domain type of `τ₁` itself; `n > 1` requires the
  annotation's domain to be `Typ.tuple [τ₁,...,τₙ]`.
-/

open TypedTLAPlus (Typ)

/-- The checker's actual input for one declaration: `CoreTLAPlus.Declaration` at `α := Option Typ`. -/
abbrev SrcDecl := CoreTLAPlus.Declaration (Option Typ)

/-- The checker's output for one declaration. -/
abbrev Decl := TypedTLAPlus.Declaration Typ

/-- `Δ` — "operators that have been marked recursive" (`reference/thesis.txt:2114`), threaded
alongside `Γ` through a module's declarations. A `RECURSIVE` predeclaration (`.recursive`) adds
its entries here, never to `Γ`; an `.operator` definition that discharges one removes it. Kept
separate from `Γ` itself (not merged permanently) so that a later `.operator` naming the same `f`
sees `f ∉ Γ` exactly as if `RECURSIVE` had never run — `requireFresh` below needs no `Δ`-aware
carve-out as a result. -/
abbrev Δ := Std.HashMap String Typ

/-- `Γ₀` — the minimal builtin prelude. Every entry is a scheme (`Binding.isScheme := true`):
each is a genuine operator definition, so `Typ.var`s used for whatever's meant to be generic get
freshened into their own metavariable at every reference (`specializeType`,
`Elaborator/Expressions.lean`'s `inferExpr`). -/
def builtinContext : Context :=
  { named := Std.HashMap.ofList <| [
      -- Equality.
      ("=", .operator [.var "a", .var "a"] .bool),
      ("/=", .operator [.var "a", .var "a"] .bool),
      -- Boolean connectives.
      ("/\\", .operator [.bool, .bool] .bool),
      ("\\/", .operator [.bool, .bool] .bool),
      ("=>", .operator [.bool, .bool] .bool),
      ("<=>", .operator [.bool, .bool] .bool),
      ("\\neg", .operator [.bool] .bool),
      -- Sets.
      ("\\in", .operator [.var "a", .set (.var "a")] .bool),
      ("\\notin", .operator [.var "a", .set (.var "a")] .bool),
      ("\\subseteq", .operator [.set (.var "a"), .set (.var "a")] .bool),
      ("\\cup", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
      ("\\cap", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
      ("\\", .operator [.set (.var "a"), .set (.var "a")] (.set (.var "a"))),
      -- Binary, matching how the parser treats it (`Core/SurfaceTLAPlus/Syntax.lean` notes `\X` is
      -- not really a binary operator in TLA⁺'s grammar; here it has a precedence and left
      -- associativity like any other). So `A \X B \X C` is `(A \X B) \X C` and its elements are
      -- pairs whose first component is a pair, not the flat triples TLA⁺ means — a three-component
      -- product is rejected downstream by the tuple-index bound rather than accepted with the wrong
      -- shape.
      ("\\X", .operator [.set (.var "a"), .set (.var "b")] (.set (.tuple [.var "a", .var "b"]))),
      ("DOMAIN", .operator [.function (.var "a") (.var "b")] (.set (.var "a"))),
      -- Temporal/action operators. `^+`/`^*`/`^#` are deliberately excluded — no typing rule exists
      -- for them, so they're left unbound. `WellFormedness/Restrictions.lean` bans all eight names
      -- regardless of whether they're bound here — this table only decides whether referencing one
      -- is caught by that check (with a precise message) or by plain `unboundVariable` first.
      ("ENABLED", .operator [.bool] .bool),
      ("UNCHANGED", .operator [.var "a"] .bool),
      ("[]", .operator [.bool] .bool),
      ("<>", .operator [.bool] .bool),
      ("'", .operator [.var "a"] (.var "a")),
    ].map λ (name, ty) ↦ (name, { type := ty, isScheme := true, origin := .intrinsic name }) }

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- A higher-order parameter's declared arity (`0` for `x`, `k` for `F(_,...,_)` with `k` `_`s)
must match its annotated type's own operator-arity, once one is known. Arity `0` needs no check
at all — any type is a legitimate ordinary-value parameter, including an operator-shaped one. -/
private def checkParamArity (pos : SourceSpan) (param : String) (arity : Nat) (τ : Typ) : m Unit :=
  if arity = 0 then pure ()
  else match τ with
    | .operator σs _ =>
      if σs.length = arity then pure ()
      else throw (.paramArityMismatch pos param arity σs.length)
    | _ => throw (.notAnOperatorType pos τ)

/-- Names the language itself permanently reserves, whether or not `builtinContext` currently
binds one — `TypedTLAPlus.reservedTemporalActionNames`'s temporal/action names, plus `SUBSET`/
`UNION` (core set-theory primitives, not temporal/action, so kept local here rather than folded
into that list). -/
private def reservedNames : List String :=
  TypedTLAPlus.reservedTemporalActionNames ++ ["SUBSET", "UNION"]

/-- `x ∉ Γ` — every declaration rule's own freshness premise. Also rejects a name the language
permanently reserves even where nothing currently binds it (e.g. `SUBSET`, `^+`) —
`builtinContext` being incomplete must not make a reserved name look free. -/
private def requireFresh (pos : SourceSpan) (x : String) : m Unit :=
  if reservedNames.contains x then throw (.alreadyDeclared pos x)
  else do
    match (← readThe Context).lookup x with
    | some _ => throw (.alreadyDeclared pos x)
    | none => pure ()

/-- `Δ`'s entries, as `Γ`-shaped `Binding`s (`origin := .module moduleName _`, matching every
other declaration-produced binding) — for merging into `Γ` while checking an operator body
(`Γ ∪ Δ`, right-biased per `reference/thesis.txt:1716-1722`; `extendAllBindings` folds left, so
inserting `Δ`'s entries wins any clash). `isScheme := false` (the default): matches this file's
existing self-recursion convention for `.function` below (line `211`, pre-`RECURSIVE`) rather
than `builtinContext`'s `isScheme := true` — a `Δ`-bound name is *this* operator, still mid-check,
referencing itself or a sibling at one fixed type, not a generic family to instantiate fresh per
call. -/
private def Δ.asBindings (moduleName : String) (δ : Δ) : List (String × Binding) :=
  δ.toList.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName x })

/-- `Γ ⊢ D ⊣ Γ'` — checks one declaration, returning its elaborated form (`none` for `.recursive`,
which emits no `TypedTLAPlus.Declaration` — B.1) alongside the bindings `Γ'` adds over `Γ` (`[]`
for `ASSUME`/`.recursive`) and `Δ`'s own updated state. A `CONSTANT`/`VARIABLE` binding is never a
scheme (`Binding.isScheme := false`, even if its annotation mentions a `Typ.var`): a `CONSTANT` is
one fixed, if abstract, value, not a family to instantiate fresh per reference. An
`operator`/`function` definition's own binding *is* a scheme, any arity — see each case below. -/
def checkDeclaration (moduleName : String) (δ : Δ) (d : SrcDecl) :
    m (Option Decl × List (String × Binding) × Δ) := match d with
  /-
     ∀ 1 ≤ i ≤ n, xᵢ ∉ Γ
    ───────────────────────────────────────────────────── [Constants]
     Γ ⊢ CONSTANTS x₁ : τ₁, …, xₙ : τₙ ⊣ Γ, x₁ : τ₁, …, xₙ : τₙ

    (A `CONSTANT` may itself be operator-shaped — `F(_, _)` — in which case its written arity is
    checked against its annotation's own arity, the same `checkParamArity` an operator's
    higher-order parameters use. `Δ` never appears in this rule — carried through unchanged.)
  -/
  | .constants xs => do
    let xs' ← xs.mapM λ (x, arity, ann) ↦ do
      requireFresh SourceSpan.placeholder x
      let τ ← requireAnnotation SourceSpan.placeholder s!"CONSTANT `{x}`" ann
      checkParamArity SourceSpan.placeholder x arity τ
      return (x, τ)
    return (some (.constants xs'), xs'.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName x }), δ)
  /-
    Same shape as [Constants].
  -/
  | .variables xs => do
    let xs' ← xs.mapM λ (x, ann) ↦ do
      requireFresh SourceSpan.placeholder x
      return (x, ← requireAnnotation SourceSpan.placeholder s!"VARIABLE `{x}`" ann)
    return (some (.variables xs'), xs'.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName x }), δ)
  /-
     Γ ⊢ e ⇓ Bool
    ─────────────────── [Assumption]
     Γ ⊢ ASSUME e ⊣ Γ

    (`ASSUME` has no name to bind, so checking one adds nothing to `Γ`. `Δ` unchanged, same
    reason as [Constants].)
  -/
  | .assume e => do
    let e' ← checkExpr e .bool
    let e' ← resolveMVars e'
    return (some (.assume e'), [], δ)
  /-
     f ∉ Γ       Γ ∪ Δ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────── [Operator definition]
     Γ ∣ Δ ⊢ f(x₁, …, xₙ) : (τ₁, …, τₙ) ⇒ τ ≜ e ⊣ Γ, f : (τ₁, …, τₙ) ⇒ τ ∣ Δ

    (`e` is checked against `Γ ∪ Δ` (right-biased), not bare `Γ`: every sibling operator still
    pending in `Δ` — including `f` itself, if a `RECURSIVE f(...)` predeclared it — is in scope
    for the body, giving self- and mutual recursion for exactly the operators named `RECURSIVE`
    (`Δ` empty or unrelated ⟹ no-op, unchanged from before `RECURSIVE` existed). `Δ` itself is
    *not* discharged by this rule in general — only when `f ∈ Δ`, resolved below before the
    `args`/`τ` match: `f`'s own defining `==` reconciles against `Δ`'s type (no annotation ⟹ use
    `Δ`'s type directly; an annotation ⟹ warn if redundant, error if it disagrees), then `f` is
    removed from `Δ` — `f ∉ Γ` (still checked unconditionally, `Δ` never having touched `Γ`)
    already rejects a second definition, `RECURSIVE`-discharging or not.

    Zero-argument definitions (`f == e`, no parens at all) are checked against the annotation
    directly as the bare result type, not `() => τ`: a 0-ary definition is always referenced by
    bare name, never called like `Nodes()`.)
  -/
  | .operator ann f args body => do
    requireFresh (posOf body) f
    let τ ← match δ[f]?, ann with
      | none, _ => requireAnnotation (posOf body) s!"operator `{f}`" ann
      | some δτ, none => pure δτ
      | some δτ, some τ' =>
        if τ' == δτ then do
          warn (.redundantRecursiveAnnotation (posOf body) f)
          pure δτ
        else throw (.recursiveAnnotationMismatch (posOf body) f δτ τ')
    let δ' := δ.erase f
    match args, τ with
    | [], retTy => do
      let body' ← extendAllBindings (Δ.asBindings moduleName δ) (checkExpr body retTy)
      let body' ← resolveMVars body'
      return (some (.operator retTy f args body'), [(f, { type := retTy, isScheme := true, origin := .module moduleName f })], δ')
    | _, .operator paramTys retTy =>
      if paramTys.length ≠ args.length then
        throw (.arityMismatch (posOf body) paramTys.length args.length)
      else do
        (args.zip paramTys).forM λ ((x, arity), τᵢ) ↦ checkParamArity (posOf body) x arity τᵢ
        let bindings := args.map Prod.fst |>.zip paramTys
        let body' ← extendAllBindings (Δ.asBindings moduleName δ) (extendAll bindings (checkExpr body retTy))
        let body' ← resolveMVars body'
        return (some (.operator τ f args body'), [(f, { type := τ, isScheme := true, origin := .module moduleName f })], δ')
    | _, _ => throw (.notAnOperatorType (posOf body) τ)
  /-
     f ∉ Γ       ∀ 1 ≤ i ≤ n, Γ ⊢ eᵢ ⇓ Set(τᵢ)       Γ, f : ⟨τ₁, …, τₙ⟩ → τ, x₁ : τ₁, …, xₙ : τₙ ⊢ e ⇓ τ
    ──────────────────────────────────────────────────────────────────────────────────────────────── [Function definition]
     Γ ⊢ f[x₁ ∈ e₁, …, xₙ ∈ eₙ] : ⟨τ₁, …, τₙ⟩ → τ ≜ e ⊣ Γ, f : ⟨τ₁, …, τₙ⟩ → τ

    (`f` *is* in the context checking `e`, unconditionally — function definitions get
    self-recursion for free, unlike operator definitions above. `Δ` never appears in this rule —
    a `RECURSIVE`-predeclared name that a function definition happens to share is simply not
    discharged by it; it surfaces later as "declared but never defined" instead, same as any other
    undischarged `Δ` entry.)
  -/
  | .function ann f args body => do
    requireFresh (posOf body) f
    let τ ← requireAnnotation (posOf body) s!"function `{f}`" ann
    match τ with
    | .function domTy retTy => do
      let τs ← match args.length, domTy with
        | 1, τ₁ => pure [τ₁]
        | n, .tuple τs => if τs.length = n then pure τs else throw (.arityMismatch (posOf body) τs.length n)
        | _, got => throw (.notATupleType (posOf body) got)
      let args' ← (args.zip τs).mapM λ ((x, e), τᵢ) ↦ do
        return (x, ← resolveMVars (← checkExpr e (.set τᵢ)))
      -- `f` is in scope for its own body (self-recursion), resolved through `Ξ` like any
      -- module-level name; the parameters are lexical binders (`Origin.bound`).
      let body' ← extendAllBindings [(f, { type := τ, origin := .module moduleName f })]
        (extendAll (args.map Prod.fst |>.zip τs) (checkExpr body retTy))
      let body' ← resolveMVars body'
      return (some (.function τ f args' body'), [(f, { type := τ, isScheme := true, origin := .module moduleName f })], δ)
    | _ => throw (.notAFunctionType (posOf body) τ)
  /-
     ∀ 1 ≤ i ≤ n, fᵢ ∉ Γ       ∀ 1 ≤ i ≤ n, fᵢ ∉ Δ
    ───────────────────────────────────────────────── [Recursive]
     Γ ∣ Δ ⊢ RECURSIVE f₁ : τ₁, …, fₙ : τₙ ⊣ Γ ∣ Δ, f₁ : τ₁, …, fₙ : τₙ

    (Adds every entry to `Δ` only — `Γ` is untouched, so this rule alone makes no name
    referenceable outside another operator definition's body (the [Operator definition] rule
    above is the only place `Δ` is read). `fᵢ ∉ Δ` also rejects a duplicate name reused within one
    `RECURSIVE` list or across two, in addition to `fᵢ ∉ Γ`'s ordinary collision check.)
  -/
  | .recursive xs => do
    let δ' ← xs.foldlM (init := δ) λ δ (x, arity, ann) ↦ do
      requireFresh SourceSpan.placeholder x
      if δ.contains x then throw (.alreadyDeclared SourceSpan.placeholder x)
      let τ ← requireAnnotation SourceSpan.placeholder s!"RECURSIVE operator `{x}`" ann
      checkParamArity SourceSpan.placeholder x arity τ
      return δ.insert x τ
    return (none, [], δ')

/-- `Γ ∣ Δ ⊢ D₁, …, Dₙ ⊣ Γ' ∣ Δ'` — checks a whole declaration list, threading `Γ` and `Δ` through
each one. Returns the accumulated `Γ' \ Γ` bindings alongside the checked declarations (`.recursive`
contributing no `Decl` at all — `Option.toList`'s `[]` case) and `Δ`'s final state, so a caller
spanning more than one such list (`declarations₁`/`declarations₂` either side of the embedded
PlusCal algorithm, `Elaborator.lean`) can thread `Δ` across both and, only once both are checked,
report any name still pending. -/
def checkDeclarations (moduleName : String) (δ : Δ) : List SrcDecl → m (List Decl × List (String × Binding) × Δ)
  | [] => return ([], [], δ)
  | d :: ds => do
    let (d', bindings, δ') ← checkDeclaration moduleName δ d
    let (ds', restBindings, δ'') ← extendAllBindings bindings (checkDeclarations moduleName δ' ds)
    return (d'.toList ++ ds', bindings ++ restBindings, δ'')

end
