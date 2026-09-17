module

public import Network2Go.Expression

public section

/-!
  Compiling TLA⁺ operator and function definitions into Go top-level declarations.

  Four forms, and which one a declaration takes is read off its *type*, not its syntax:

  - **A parameter-less operator** (`X == e`) becomes a package-level `var X τ = ⟦e⟧`. Not a `const`:
    Go accepts only a small class of types there, and a TLA⁺ definition generally has none of them.
    Immutability is a convention here rather than something Go enforces.
  - **A parametric operator** (`X(p₁, …, pₙ) == e`) becomes an ordinary Go function. Go supports
    mutually recursive top-level functions natively, so nothing special is needed — and in this
    compiler an operator is never recursive at all: `RECURSIVE` is out of the accepted language, and
    `Elaborator/Declarations.lean`'s `[Operator definition]` rule checks the body without the
    operator itself in `Γ`. The thesis's mutually-recursive `Even`/`Odd` example is unreachable.
  - **A non-recursive function definition** (`F[x ∈ D] == e`) becomes `var F = FnConstructor(…)`.
  - **A recursive function definition** becomes `var F = MkRecFn(…)`, which ties the knot: it
    allocates the `LazyFunction` with no generator, then overwrites the generator with a closure
    that captures the function itself. Unlike operators, a function definition *always* gets
    self-recursion (`[Function definition]` binds `f` while checking the body), so which of the two
    to emit is decided by looking for the self-reference rather than by a keyword.

  **Type variables reach only the parametric-operator form.** A rigid type variable compiles to a
  Go type parameter, and each one carries a dictionary parameter beside it, since a polymorphic
  definition is called at many types and its ordering therefore cannot be a closed expression. Go
  has no generic package-level `var`, so the other three forms — all of which are `var`s — must
  reject one. That is a restriction of Go's, not a choice: there is nowhere to bind the parameter.

  `CONSTANT`/`VARIABLE` declarations and `ASSUME` produce nothing. A `CONSTANT` is supplied by
  whoever wires the generated code into a runnable system, under the capitalized name every
  reference to it compiles to — the same boundary the absence of an emitted `main` sits on. An
  `ASSUME` is a proof obligation about a specification, with no computational content to emit.
-/

namespace Network2Go

open ComputableTLAPlus (Typ)

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m] [MonadFresh m]

/-- Does `name` occur in `e` as a reference to the enclosing function *definition* being checked?

A function definition's body sees its own name in scope, resolved through `Ξ` like any
module-level name (`.module`); a bare occurrence of `name` inside `name`'s own body is therefore a
self-reference. The caller has already ruled out a parameter of the same name, so the check is
exact and no binder-respecting scope walk is needed. -/
partial def mentionsSelf (name : String) (e : ComputablePlusCal.Expression) : Bool :=
  let go := mentionsSelf name
  match_source e with
  | .var _ (.module _ x), _ => x == name
  | .var .., _ | .nat _, _ | .str _, _ | .true, _ | .false, _ => false
  | .opCall f args, _ => go f || args.any go
  | .forall _ _ d b, _ | .exists _ _ d b, _ | .choose _ _ d b, _ | .collect _ _ d b, _ =>
    go d || go b
  | .set es _, _ | .seq es _, _ => es.any go
  | .map' b _ _ _ d, _ => go b || go d
  | .fn _ _ _ d b, _ => go d || go b
  | .fnCall f _ i, _ => go f || go i
  | .record fs, _ => fs.any λ (_, _, e') ↦ go e'
  | .except f _ upds, _ =>
    go f || upds.any λ (path, rhs) ↦
      go rhs || path.any λ | .inl _ => false | .inr i => go i
  | .recordAccess r _, _ => go r
  | .tuple es, _ => es.any λ (_, e') ↦ go e'
  | .if c t f _, _ => go c || go t || go f
  | .case arms other _, _ =>
    arms.any (λ (p, b) ↦ go p || go b) || (other.map go).getD false

/-- Rewrite a function definition body's self-reference — `.module _ f`, since `f` is in scope for
its own body — to the free name `f`, which is what `MkRecFn`'s generator parameter is called. -/
private def bindSelf (f : String) (e : ComputablePlusCal.Expression) : ComputablePlusCal.Expression :=
  e.mapVars (λ _ τ o pos ↦ match o with
    | .module _ n => if n == f then .var τ (.free n) @@ pos else .var τ o @@ pos
    | _ => .var τ o @@ pos) 0

/-- The Go type parameters a definition of type `τ` binds, each paired with the dictionary
parameter that carries its ordering. Type parameters are unconstrained (`any`): the ordering
travels as a value, which is the whole point of the dictionary representation.

The dictionary's type argument goes through `binderName` exactly as the type parameter itself does,
and for a sharper reason than consistency: a type variable named after a predeclared identifier
would otherwise leave `Ord[int]` referring to *Go's* `int` while the parameter it is meant to order
is the renamed `int_`. That reads as well-typed and means something else. -/
private def genericParams (τ : Typ) : List (String × Go.Typ) × List (String × Go.Typ) :=
  let vars := Typ.typeVars τ
  ( vars.map λ a ↦ (binderName a, .named "any" []),
    vars.map λ a ↦ (ordParamName a, tlaplusTyp "Ord" [.var (binderName a)]) )

/-- A form that compiles to a package-level `var` cannot be polymorphic — Go has no generic `var`.
`what` names the form, for the diagnostic. -/
private def requireMonomorphic (pos : SourceSpan) (what name : String) (τ : Typ) : m Unit :=
  if (Typ.typeVars τ).isEmpty then pure () else
    throw (.unsupported pos s!"{what} '{name}'"
      "it compiles to a package-level Go variable, and Go has no generic variables — only a \
       parametric operator can carry type parameters")

/-- Builds `Set(Typ.tuple τs)` from `n ≥ 2` per-binder domain sets (`doms'`, same order as `τs`),
by chaining `SetProduct` — binary, Go has no variadic generic — so each step's pairing closure
destructures the accumulated prefix tuple and repacks a flat, one-field-longer tuple, never a
nested pair: matches the flat `Typ.tuple τs` domain type checking already assigned the
definition, and what a multi-index call `f[e₁,…,eₙ]` already indexes with
(`CoreTLAPlus.Expression.fnCall`'s own doc comment). No new runtime primitive — `SetProduct`
already builds exactly this flat shape for `n = 2` (`"\X"`'s own codegen,
`Network2Go/Expression.lean`); this generalizes it to any `n` by feeding its own output back in as
one side of the next call. -/
private def buildProductDomain (pos : SourceSpan) :
    List Typ → List ComputableGo.Expression → m ComputableGo.Expression
  | τ₁ :: τs, dom₁ :: doms => go [τ₁] dom₁ τs doms
  | _, _ => throw (.internalInvariantViolated pos
      "a function definition's domain-tuple types and compiled domains disagreed in length")
where
  /-- `pre`: the component types folded into `acc` so far, in binder order. `acc`'s own Go type is
  `τ₁` bare when `pre.length = 1` (nothing paired yet), the flat `pre`-shaped tuple struct once
  `pre.length ≥ 2`. -/
  go (pre : List Typ) (acc : ComputableGo.Expression) :
      List Typ → List ComputableGo.Expression → m ComputableGo.Expression
    | [], [] => return acc
    | τᵢ :: restτ, domᵢ :: restDom => do
      let p ← goIdent <$> freshName "x"
      let q ← goIdent <$> freshName "y"
      let preGoτ ← compileTyp (match pre with | [τ] => τ | _ => .tuple pre)
      let elemGoτ ← compileTyp τᵢ
      let pre' := pre ++ [τᵢ]
      let resultGoτ ← compileTyp (.tuple pre')
      let preFields :=
        if pre.length = 1 then [(projName 1, Go.Expression.var p)]
        else (List.range pre.length).map λ k ↦
          (projName (k + 1), Go.Expression.field (.var p) (projName (k + 1)))
      let fields := preFields ++ [(projName (pre.length + 1), Go.Expression.var q)]
      let pairClosure := Go.Expression.funcLit [(p, preGoτ), (q, elemGoτ)] [resultGoτ]
        [.return [.structLit resultGoτ fields]]
      go pre' (tlaplusCall "SetProduct" [acc, domᵢ, pairClosure]) restτ restDom
    | _, _ => throw (.internalInvariantViolated pos
        "a function definition's domain-tuple types and compiled domains disagreed in length")

/--
  Compiles one top-level declaration, or nothing for the ones with no computational content.
-/
def compileDeclaration (pos : SourceSpan) :
    ComputableTLAPlus.Declaration Typ → m (Option ComputableGo.Declaration)
  | .constants _ | .variables _ | .assume _ => return none
  | .operator τ f [] body => do
    -- `X == e`: the annotation is the result type directly, not `() => τ` — a parameter-less
    -- definition is referenced by bare name and never called.
    requireMonomorphic pos "the definition" f τ
    return some (.var (definitionName (isLocal := false) f) (← compileTyp τ) (some (← compileExprTop body)))
  | .operator τ f args body => do
    let .operator paramTys ret := τ
      | throw (.internalInvariantViolated pos
          s!"operator '{f}' takes arguments but its type is {repr τ}, which type checking should \
             already have rejected")
    if paramTys.length ≠ args.length then
      throw (.internalInvariantViolated pos
        s!"operator '{f}' has {args.length} parameters but {paramTys.length} parameter types")
    let (typeParams, dictParams) := genericParams τ
    -- Parameter names are left as written: capitalization applies to definitions, not to the
    -- variables bound inside them, and every reference to one compiles as an ordinary binder.
    let params ← (args.zip paramTys).mapM λ ((x, _arity), τᵢ) ↦ return (binderName x, ← compileTyp τᵢ)
    return some (.function
      { name := definitionName (isLocal := false) f
        typeParams, params := dictParams ++ params
        returnType := [← compileTyp ret]
        body := [.return [← compileExprTop body (args.map Prod.fst)]] })
  | .function τ f args body => do
    requireMonomorphic pos "the function definition" f τ
    let .function domτ ranτ := τ
      | throw (.internalInvariantViolated pos
          s!"function '{f}' has type {repr τ}, which type checking should already have rejected")
    -- With the same name as a binder, `MkRecFn`'s generator would take two parameters called `f`.
    if args.any (·.1 == f) then
      throw (.unsupported pos s!"the function definition '{f}'"
        "one of its binders shadows its own name, so a recursive reference could not be told from \
         a reference to the binder")
    let goτ ← compileTyp τ
    let dict ← ordDict domτ
    let paramτ ← compileTyp domτ
    let retτ ← compileTyp ranτ
    -- `genParam`/`destructure`: the generator's own Go parameter, plus (arity ≥ 2 only) the local
    -- `var`/`=` pair that opens its tuple struct back into `x₁,…,xₙ`, each bound under the same
    -- `binderName` an operator's own parameters already use, so `compileExprTop`'s existing
    -- per-name resolution below needs no change at all — arity 1's parameter *is* `x`, unchanged.
    let step : m (String × List ComputableGo.Statement × ComputableGo.Expression) := match args with
      | [(x, dom)] => do return (binderName x, [], ← compileExprTop dom)
      | (_, _) :: (_, _) :: _ => do
        let .tuple τs := domτ
          | throw (.internalInvariantViolated pos
              s!"function '{f}' takes {args.length} binders but its domain type is {repr domτ}, \
                 which type checking should already have rejected")
        if τs.length ≠ args.length then
          throw (.internalInvariantViolated pos
            s!"function '{f}' takes {args.length} binders but its domain type has {τs.length} \
               components, which type checking should already have rejected")
        let doms' ← args.mapM λ (_, dom) ↦ compileExprTop dom
        let dom' ← buildProductDomain pos τs doms'
        let tupleParam ← goIdent <$> freshName "tuple"
        let destructure ← (args.zip τs).zipIdx.mapM λ (((x, _), τᵢ), i) ↦ do
          let xGoτ ← compileTyp τᵢ
          return [Go.Statement.var (binderName x) xGoτ,
            Go.Statement.assign [.var (binderName x)] [.field (.var tupleParam) (projName (i + 1))]]
        return (tupleParam, destructure.flatten, dom')
      | [] => unreachable!
    let (genParam, destructure, dom') ← step
    -- The body sees `f` in scope through `Ξ` (`.module`); the recursive knot is tied by `MkRecFn`'s
    -- generator parameter, an ordinary binder named after `f`, so the self-reference is rewritten
    -- to that free name. Each `xᵢ` is a de Bruijn binder, opened to its own name — `destructure`
    -- above gives it a value to resolve to when the generator takes one Go parameter (arity ≥ 2).
    let body' ← compileExprTop (bindSelf f body) (args.map Prod.fst)
    -- The self-reference compiles to the *original* name, so naming the generator's first parameter
    -- after it is exactly what closes the loop. The top-level `var` is capitalized and so cannot
    -- collide with it.
    let value :=
      if mentionsSelf f body then
        tlaplusCall "MkRecFn"
          [dict, dom', .funcLit [(binderName f, goτ), (genParam, paramτ)] [retτ]
            (destructure ++ [Go.Statement.return [body']])]
      else
        tlaplusCall "FnConstructor"
          [dict, dom',
            .funcLit [(genParam, paramτ)] [retτ] (destructure ++ [Go.Statement.return [body']])]
    return some (.var (definitionName (isLocal := false) f) goτ (some value))

/-- A whole declaration list, keeping only what compiles to something. Order is preserved: Go
resolves package-level declarations independently of the order they are written in, so this matters
for readability rather than for correctness. -/
def compileDeclarations (pos : SourceSpan) (ds : List (ComputableTLAPlus.Declaration Typ)) :
    m (List ComputableGo.Declaration) :=
  return (← ds.mapM (compileDeclaration pos)).reduceOption

end Network2Go

end
