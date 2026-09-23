module

public import Elaborator.Subtyping
public import Elaborator.TypeUtils

public section

open TypedTLAPlus (Typ MVarId Expr)

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty). -/
private local instance {α} [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

/-- Substitutes every already-assigned metavariable inside `τ`, recursing into whatever
`onUnassigned` returns for one that isn't. Shared by `resolveTypeMVars` (throws: every
metavariable must be resolved by the time a declaration finishes checking) and
`instantiateMVars` below (best-effort: an unresolved one is left as `Typ.mvar n`). -/
private partial def resolveTypeMVarsWith (onUnassigned : MVarId → m Typ) : Typ → m Typ
  | .mvar n => do
    match ← assigned? n with
    | some τ' => resolveTypeMVarsWith onUnassigned τ'
    | none => onUnassigned n
  | .var a => return .var a
  | .bool => return .bool
  | .int => return .int
  | .str => return .str
  | .address => return .address
  | .const c => return .const c
  | .function dom rng =>
    return .function (← resolveTypeMVarsWith onUnassigned dom) (← resolveTypeMVarsWith onUnassigned rng)
  | .set τ => return .set (← resolveTypeMVarsWith onUnassigned τ)
  | .seq τ => return .seq (← resolveTypeMVarsWith onUnassigned τ)
  | .channel τ => return .channel (← resolveTypeMVarsWith onUnassigned τ)
  | .bag τ => return .bag (← resolveTypeMVarsWith onUnassigned τ)
  | .tuple τs => return .tuple (← τs.mapM (resolveTypeMVarsWith onUnassigned))
  | .operator τs τ =>
    return .operator (← τs.mapM (resolveTypeMVarsWith onUnassigned)) (← resolveTypeMVarsWith onUnassigned τ)
  | .record fs => return .record (← fs.mapM λ (x, τ) ↦ return (x, ← resolveTypeMVarsWith onUnassigned τ))

private def resolveTypeMVars (pos : SourceSpan) : Typ → m Typ :=
  resolveTypeMVarsWith λ _ ↦ throw (.unconstrainedMetavariable pos)

/-- Best-effort metavariable substitution for a `Typ`, named after `Lean.Meta.instantiateMVars`
since it does the same job for the same reason: an already-resolved metavariable (e.g. pinned by
an earlier operand in the same call) is substituted with its solution; one that's never been
constrained is left as `Typ.mvar n` (rendered `?n`) rather than erroring. Needed wherever a `Typ`
is about to be embedded in a thrown `TCError` (so the message shows a concrete type instead of a
raw `?n`), and wherever a `Typ` obtained from `inferExpr` is about to be pattern-matched against a
specific shape (`.record`/`.set`/`.function`/…): a scheme operator's result can carry a
metavariable its own argument-checking already solved, but nothing rewrites the `Typ` tree in
place, so a bare structural match sees `.mvar n` and not the solution — e.g. `\E m \in DOMAIN
someBag : m.field` elaborates `m.field` only because `m`'s type is instantiated first. Read-only
over the metavariable context, so calling it anywhere never affects checking's soundness, only
whether an already-decided type is visible yet. -/
def instantiateMVars : Typ → m Typ :=
  resolveTypeMVarsWith (pure ∘ .mvar)

/-- Every type stored anywhere in `e`, pending-coercion wrappers' source and target included. -/
private def exprTypes (e : Expr) : List Typ :=
  (Id.run ((TypedTLAPlus.Expression.traverse (F := StateM (List Typ))
    (λ τ ↦ do modify (τ :: ·); pure τ) e).run [])).2

/-- Every metavariable reachable from `todo`, beyond those already in `seen`: through an
assignment, or through a recorded upper bound. -/
private partial def reachableMVarsFrom (todo seen : List MVarId) : m (List MVarId) := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then reachableMVarsFrom rest seen
    else do
      let next ← match ← assigned? n with
        | some τ => pure (typeMVars τ)
        | none => pure ((← pendingUpperBounds n).flatMap typeMVars)
      reachableMVarsFrom (next ++ rest) (n :: seen)

/-- Every upper bound on `n` that is not itself an unresolved metavariable, assignments
substituted. A bound that *is* one contributes its own bounds instead: `?n <: ?c <: τ` makes `τ`
a bound on `?n` too. -/
private partial def transitiveBounds (n : MVarId) (seen : List MVarId := []) : m (List Typ) := do
  if seen.contains n then return []
  let mut out := []
  for b in ← pendingUpperBounds n do
    match ← instantiateMVars b with
    | .mvar c => out := out ++ (← transitiveBounds c (n :: seen))
    | b' => out := out ++ [b']
  return out.eraseDups

/-- `instantiateMVars`, except that a type still a bare unresolved metavariable is shown as one of
its upper bounds when it has any — what an error message should call the type, rather than `?n`. -/
def displayType (τ : Typ) : m Typ := do
  let τ ← instantiateMVars τ
  let .mvar n := τ | return τ
  match ← transitiveBounds n with
  | b :: _ => return b
  | [] => return τ

/-- Defaults every unresolved metavariable reachable from `roots` that has upper bounds (directly,
or through other metavariables) to the tightest of them, repeating until nothing more can be
defaulted — one defaulting can resolve a metavariable another's bounds mention. A metavariable with
no such bound is left unresolved. Two bounds with no common subtype are a
`TCError.conflictingUpperBounds` error. -/
partial def defaultMVars (pos : SourceSpan) (roots : List MVarId) : m Unit := do
  let mut progress := false
  for n in ← reachableMVarsFrom roots [] do
    if (← assigned? n).isNone then
      let bounds ← transitiveBounds n
      if let b :: bs := bounds then
        let g ← bs.foldlM (init := b) λ acc b' ↦ do
          match ← glb acc b' with
          | some g => pure g
          | none => throw (.conflictingUpperBounds pos (← instantiateMVars acc) (← instantiateMVars b'))
        match ← subtype g (.mvar n) with
        | .success _ => progress := true
        | .pending _ => throw (.unconstrainedMetavariable pos)
        | .failure => throw (.conflictingUpperBounds pos (← instantiateMVars g) (← instantiateMVars b))
  if progress then defaultMVars pos roots

/-- Merges the still-unresolved metavariables reachable from `roots` that are bounded only by one
another: each is assigned to its first bound that is another unresolved metavariable, so every
such group ends up sharing one representative. Satisfies every bound between them, since `τ <:
τ`. -/
private def collapseMVars (roots : List MVarId) : m Unit := do
  for n in ← reachableMVarsFrom roots [] do
    if (← assigned? n).isNone then
      for b in ← pendingUpperBounds n do
        if let .mvar c ← instantiateMVars b then
          if c != n then assignMVar n (.mvar c)

/-- `k` type-variable names, none of them in `taken`: `a`, …, `z`, then `a1`, …. -/
private def freshTypeVarNames (taken : List String) (k : Nat) : List String :=
  let candidates := (List.range (k + taken.length)).map λ i ↦
    let letter := String.singleton (Char.ofNat ('a'.toNat + i % 26))
    if i < 26 then letter else letter ++ toString (i / 26)
  (candidates.filter (!taken.contains ·)).take k

/-- Closes out a definition with no annotation, whose signature is `sig` and whose elaborated
parts are `es`: defaults every metavariable that can be defaulted, merges those bounded only by one
another, and turns each one still left in `sig` into a fresh rigid type variable. Returns the
resulting signature, generalized over those variables. `es` still need `resolveMVars`, which
rejects any metavariable left that `sig` does not mention. -/
def generalizeMVars (pos : SourceSpan) (sig : Typ) (es : List Expr) : m Typ := do
  let roots := typeMVars sig ++ es.flatMap λ e ↦ (exprTypes e).flatMap typeMVars
  defaultMVars pos roots
  collapseMVars roots
  let open_ := (typeMVars (← instantiateMVars sig)).eraseDups
  let taken := es.flatMap λ e ↦ (exprTypes e).flatMap typeFreeVars
  for (n, a) in open_.zip (freshTypeVarNames taken open_.length) do
    assignMVar n (.var a)
  instantiateMVars sig

/--
  Eliminates every `mvar` node inside `e`, walking bottom-up so a nested `mvar` resolves before
  an outer one that might wrap it. Each node's coercion is recomputed from its own source and
  target types, now that the metavariables they mention are resolved.

  Only eliminates `Expression.mvar` wrapper nodes, not `Typ.mvar` occurrences embedded in a node's
  stored type field — those are resolved by `resolveMVars` below, as a second pass.
-/
private partial def resolveExprMVars (e : Expr) : m Expr := match_source e with
  | .var τ o, pos => return .var τ o @@ pos
  | .nat n, pos => return .nat n @@ pos
  | .str s, pos => return .str s @@ pos
  | .true, pos => return .true @@ pos
  | .false, pos => return .false @@ pos
  | .opCall f args, pos => return .opCall (← resolveExprMVars f) (← args.mapM resolveExprMVars) @@ pos
  | .forall x τ dom body, pos =>
    return .forall x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .exists x τ dom body, pos =>
    return .exists x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .fforall x τ body, pos => return .fforall x τ (← resolveExprMVars body) @@ pos
  | .eexists x τ body, pos => return .eexists x τ (← resolveExprMVars body) @@ pos
  | .choose x τ dom body, pos =>
    return .choose x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .set es τ, pos => return .set (← es.mapM resolveExprMVars) τ @@ pos
  | .collect x τ dom pred, pos =>
    return .collect x τ (← resolveExprMVars dom) (← resolveExprMVars pred) @@ pos
  | .map' body x τ cod dom, pos =>
    return .map' (← resolveExprMVars body) x τ cod (← resolveExprMVars dom) @@ pos
  | .fnCall f fnTyp idx, pos =>
    return .fnCall (← resolveExprMVars f) fnTyp (← resolveExprMVars idx) @@ pos
  | .fn x τ cod dom body, pos =>
    return .fn x τ cod (← resolveExprMVars dom) (← resolveExprMVars body) @@ pos
  | .fnSet dom cod, pos => return .fnSet (← resolveExprMVars dom) (← resolveExprMVars cod) @@ pos
  | .record fields, pos =>
    return .record (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .recordSet fields, pos =>
    return .recordSet (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .except e τ upds, pos => do
    let e' ← resolveExprMVars e
    let upds' ← upds.mapM λ (path, newVal) ↦ do
      let path' ← path.mapM λ
        | .inl field => return (Sum.inl field : String ⊕ Expr)
        | .inr idx => return .inr (← resolveExprMVars idx)
      return (path', ← resolveExprMVars newVal)
    return .except e' τ upds' @@ pos
  | .recordAccess e x, pos => return .recordAccess (← resolveExprMVars e) x @@ pos
  | .tuple es, pos => return .tuple (← es.mapM λ (τ, e) ↦ return (τ, ← resolveExprMVars e)) @@ pos
  | .seq es τ, pos => return .seq (← es.mapM resolveExprMVars) τ @@ pos
  | .if c t f τ, pos =>
    return .if (← resolveExprMVars c) (← resolveExprMVars t) (← resolveExprMVars f) τ @@ pos
  | .case branches other τ, pos => do
    let branches' ← branches.mapM λ (p, e) ↦ return (← resolveExprMVars p, ← resolveExprMVars e)
    return .case branches' (← other.mapM resolveExprMVars) τ @@ pos
  | .stutter e a, pos => return .stutter (← resolveExprMVars e) (← resolveExprMVars a) @@ pos
  | .mvar src tgt e, pos => do
    let e' ← resolveExprMVars e
    match ← subtype src tgt with
    | .success coe => return coe.apply e' @@ pos
    | .pending _ => throw (.unconstrainedMetavariable pos)
    | .failure => throw (.failedToConvertTypes pos (← displayType tgt) (← displayType src))

/-- Closes out an elaborated expression: defaults every metavariable it reaches that has an upper
bound (`defaultMVars`), eliminates every `Expression.mvar` wrapper node (`resolveExprMVars`),
then walks the result once more resolving any `Typ.mvar` left behind in a stored type field. -/
partial def resolveMVars (e : Expr) : m Expr := do
  defaultMVars (posOf e) ((exprTypes e).flatMap typeMVars)
  let e' ← resolveExprMVars e
  TypedTLAPlus.Expression.traverse (resolveTypeMVars (posOf e')) e'

end
