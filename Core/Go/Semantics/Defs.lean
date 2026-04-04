import Core.Go.Semantics.Domains
import Core.Go.Syntax

/-!
  Now that we have finished defining our domains…we can finally define the semantics of
  Go.
-/

abbrev Address := PUnit ⊕ PUnit ⊕ ℕ

abbrev nil : Address := .inl .unit
abbrev dummy : Address := .inr (.inl .unit)
instance : Coe ℕ Address := ⟨λ x ↦ .inr (.inr x)⟩

abbrev Channel := ℕ

instance : CompleteSpace Channel := sorry

abbrev 𝕍 := Restriction Value.𝕍.type unitInterval.half

structure Store where
  /-- The main memory -/
  ϙ : Address → Option 𝕍
  /-- Scopes, i.e. a stack of bindings from variable names to addresses. -/
  h : List (String → Option Address)
  deriving Nonempty

def Store.toProd (s : Store) : (Address → Option 𝕍) × List (String → Option Address) :=
  (s.ϙ, s.h)

theorem Store.toProd_injective : Function.Injective Store.toProd := by
  rintro ⟨ϙx, hx⟩ ⟨ϙy, hy⟩ (_|_)
  rfl

noncomputable instance : IMetricSpace Store :=
  .induced _ Store.toProd_injective inferInstance

instance : CompleteSpace Store := sorry

abbrev 𝔽 :=
  List 𝕍 × List Channel × (String → Option Channel) → Domain Store Channel 𝕍 PUnit

noncomputable section
  open TypedSetTheory (Expression Typ)

  namespace TypedSetTheory.Expression
    protected def denotation (χ : String → Option 𝔽) (ξ : List Channel) (ς : String → Option Channel) : Expression Typ → Domain Store Channel 𝕍 𝕍
      | _ => sorry
  end TypedSetTheory.Expression

  namespace GoCal
    namespace Statement
      variable {out : Channel}

      set_option trace.Meta.synthInstance true in
      set_option trace.Meta.isDefEq true in
      protected def denotation (χ : String → Option 𝔽) (ξ : List Channel) (ς : String → Option Channel) : Statement Typ (Expression Typ) Typ.initArgs → Domain Store Channel 𝕍 PUnit
        | .panic e => e.denotation χ ξ ς |>.bind λ _ ↦ .abort
        | _ => sorry
    end Statement
  end GoCal
end
