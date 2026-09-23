module

public import Core.Go.Semantics.Domains
public import Core.Go.Semantics.Operations
public import Core.Go.Syntax
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

open scoped UniformConvergence Domain

/-!
  Go-specific semantics, built on the domain theory of `Domains.lean`/`Operations.lean`.
-/

open Classical in
/-- `Go.Typ`'s equality, decided classically: nothing in the compiler pipeline computes it, it
exists only to satisfy `IMetricSpace.discrete`'s constraint below. -/
noncomputable instance : DecidableEq Go.Typ := λ a b ↦ propDecidable (a = b)

/-- `Go.Typ`'s metric: discrete, since `Value.𝕍`'s `Typ` parameter is opaque throughout
`Domains.lean` — nothing there inspects which two types are equal, only whether they are. -/
noncomputable instance : DiscreteIMetricSpace Go.Typ where
  __ := IMetricSpace.discrete

instance : CompleteSpace Go.Typ := DiscreteIMetricSpace.completeSpace

theorem ENNReal.toReal_two : ENNReal.toReal 2 = 2 := rfl

abbrev Address : Type := PUnit ⊕ PUnit ⊕ ℕ

abbrev nil : Address := .inl .unit
abbrev dummy : Address := .inr (.inl .unit)
instance : Coe ℕ Address := ⟨λ x ↦ .inr (.inr x)⟩

def Channel := ℕ × Go.Typ

open Classical in
noncomputable instance : DecidableEq Channel := λ a b ↦ propDecidable (a = b)

noncomputable instance : DiscreteIMetricSpace Channel where
  __ := IMetricSpace.discrete
instance : CompleteSpace Channel := DiscreteIMetricSpace.completeSpace

-- TODO(go-semantics): define `Store` mutually with `𝕍` instead of axiomatizing it.
axiom Store : NonemptyType.{0}

instance : Nonempty Store.type := Store.property

@[instance]
axiom Store_metricspace : IMetricSpace Store.type

@[instance]
axiom Store_ultrametricspace : IsUltrametricIDist Store.type

@[instance]
axiom Store_completespace : CompleteSpace Store.type

open Classical in
axiom Store_iso :
  Store.type ≃ᵢ (Address →ᵤ Option (Value.𝕍 Store.type Channel Address Go.Typ).type) × List (String →ᵤ Option Address)

noncomputable def Store.type.h : Store.type → Address → Option (Value.𝕍 Store.type Channel Address Go.Typ).type :=
  Prod.fst ∘ ⇑Store_iso

noncomputable def Store.type.ϙ : Store.type → List (String → Option Address) :=
  Prod.snd ∘ ⇑Store_iso

open Classical in
noncomputable def Store.popϙ (σ : Store.type) : Option Store.type := match Store.type.ϙ σ with
  | [] => .none
  | _ :: ϙ => .some (⇑Store_iso.symm ⟨Store.type.h σ, ϙ⟩)

noncomputable def Store.deref (σ : Store.type) (addr : Address) : Option (Value.𝕍 Store.type Channel Address Go.Typ).type :=
  Store.type.h σ addr

open Classical in
noncomputable def Store.update (σ : Store.type) (addr : Address) (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) : Option Store.type :=
  -- Check that the address is allocated
  Store.deref σ addr |>.bind λ _ ↦
    let h' := Function.update (Store.type.h σ) addr (.some v)
    pure (Store_iso.symm (h', Store.type.ϙ σ))

noncomputable section
  open scoped Domain

  /-! # Some helpers -/

  def boolean {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α) (f : Bool → α) : α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      f
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      v

  def integer {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α) (f : ℤ → α) : α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      f
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      v

  def array {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α)
    (f : (n : ℕ) → (Fin n →ᵤ Address) → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      f
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      v

  def channel {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α)
    (async : Address → Go.Typ → Address → Address → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      async
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      v

  /-! # The main semantics -/

  open Classical

  namespace Go.Expression
    protected def denotation (ξ : List Channel) (ς : String → Option Channel) :
        Go.Expression Go.Typ → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type
      | _ => Domain.branch sorry

    protected def denotations (ξ : List Channel) (ς : String → Option Channel) :
        List (Go.Expression Go.Typ) → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (List (Value.𝕍 Store.type Channel Address Go.Typ).type)
      | [] => .pure []
      | e :: es => Go.Expression.denotation ξ ς e >>= λ v ↦ (v :: ·) <$> Go.Expression.denotations ξ ς es
  end Go.Expression

  namespace Go.Statement
    variable (out : Channel)

    def zero (σ : Store.type) : Go.Typ → Store.type × (Value.Send𝕍 Address Go.Typ)
      | .bool => (σ, .bool false)
      | .int => (σ, .int 0)
      | .str => (σ, .str "")
      | .map _ _ => (σ, .map [] true)
      | .chan _ => sorry
      | .slice _ => sorry
      | .array _ _ => sorry
      | .struct _ => sorry
      | .func _ _ => sorry
      | .named _ _ => sorry
      | .var _ => sorry

    instance : HasDefaultInit Store.type Channel (Value.Send𝕍 Address Go.Typ) where
      zero c σ := zero σ (Prod.snd c)

    def guard (ξ : List Channel) (ς : String → Option Channel) (e : Go.Expression Go.Typ) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
      Go.Expression.denotation ξ ς e >>= λ v ↦ Domain.branch λ σ ↦
        boolean v (default := {.next σ { val := .abort }})
          λ b ↦ if b then {.next σ { val := .pure .unit }} else ∅

    theorem guard.is_branch {ξ ς e} : ∃ f, guard ξ ς e = Domain.branch f := by
      unfold guard
      admit

    def deref (σ : Store.type) (addr : Address) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type :=
      match Store.deref σ addr with
      | .some v => .pure v
      | .none => .abort

    def for_seq_F (ξ : List Channel) (ς : String → Option Channel) (e : Go.Expression Go.Typ)
        (P' P : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
      (P ⬰ P' ⬰ guard ξ ς e) ⊻ (.pure .unit ⬰ guard ξ ς (.unary .not e))

    def for_seq (ξ : List Channel) (ς : String → Option Channel) (e : Go.Expression Go.Typ)
        (P : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit) :
        ℕ → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit
      | 0 => .branch λ σ ↦ {.next σ { val := .pure .unit }}
      | i + 1 => for_seq_F ξ ς e P (for_seq ξ ς e P i)

    protected def denotation (out : Channel) (ξ : List Channel) (ς : String → Option Channel) :
        List ComputableGo.Statement → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit
      | [] => .branch λ σ ↦ {.next σ { val := .pure .unit }}
      | .panic e :: ss => Go.Statement.denotation out ξ ς ss ⬰ (Go.Expression.denotation ξ ς e >>= λ _ ↦ Domain.abort)
      | .return es :: ss => match ss with
        | [] => match ξ with
          | ret :: _ => Go.Expression.denotations ξ ς es >>= λ vs ↦ Domain.branch λ σ ↦ match Store.popϙ σ with
            | .none => {.next σ { val := .abort }}
            | .some σ => {.next σ {
              val := if h : ∀ v ∈ vs, Value.𝕍_isSend v then
                .branch λ _ ↦ {.send ret (Value.𝕍_extract (Value.𝕍.tuple vs) (Value.𝕍_isSend.tuple h)) { val := .pure .unit }}
              else
                .abort
            }}
          | [] => .branch λ σ ↦ {.next σ { val := .abort }}
        | _ => .branch λ σ ↦ {.next σ { val := .abort }}
      | .print e :: ss =>
        Go.Statement.denotation out ξ ς ss ⬰ (Go.Expression.denotation ξ ς e >>= λ v ↦
          if h : Value.𝕍_isSend v then
            Domain.branch λ _ ↦ {.send out (Value.𝕍_extract v h) { val := .pure .unit }}
          else
            Domain.abort)
      | .if e S₁ S₂ :: ss =>
        Go.Statement.denotation out ξ ς ss ⬰ ((Go.Statement.denotation out ξ ς S₁ ⬰ guard ξ ς e) ⊻ (Go.Statement.denotation out ξ ς S₂ ⬰ guard ξ ς (.unary .not e)))
      | .for e S :: ss =>
        Go.Statement.denotation out ξ ς ss ⬰ Filter.lim (Filter.atTop.map (for_seq ξ ς e (Go.Statement.denotation out ξ ς S)))
      | .go S :: ss => (λ _ ↦ PUnit.unit) <$> (Go.Statement.denotation out ξ ς S ∥ Go.Statement.denotation out ξ ς ss)
      | .send c e :: ss =>
        Go.Expression.denotation ξ ς e >>= λ v ↦
        Go.Expression.denotation ξ ς c >>= λ c ↦
        Go.Statement.denotation out ξ ς ss ⬰ Domain.branch λ σ ↦
          channel c (default := {.next σ { val := .abort }})
            (λ len' τ buf closed? ↦
              match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
              | .none => {.next σ { val := .abort }}
              | .some (closed?, len, buf) =>
                boolean closed? (default := {.next σ { val := .abort }})
                  λ closed? ↦ integer len (default := {.next σ { val := .abort }})
                  λ len ↦ array buf (default := {.next σ { val := .abort }})
                  λ cap indices ↦
                    if h : closed? ∧ len ≥ 0 ∧ len < cap then
                      let i : Fin cap := ⟨len.toNat, propext (Int.toNat_lt h.2.1) ▸ h.2.2⟩
                      let σ' := Store.update σ (indices i) v |>.bind λ σ ↦ Store.update σ len' (Value.𝕍.int <| len + 1)
                      match σ' with
                      | .some σ' => {.next σ' { val := .pure .unit }}
                      | .none => {.next σ { val := .abort }}
                    else if closed? ∧ len ≥ cap then
                      ∅
                    else
                      {.next σ { val := .abort }}
            )
      | _ => sorry

      theorem for_seq_F_nonexpansive {ξ ς e q} :
          ∀ p p', edist (for_seq_F ξ ς e q p) (for_seq_F ξ ς e q p') ≤ (1/2) * edist p p' := by
        intros p p'
        repeat rw [Domain.edist_eq]

        have : 1 / 2 = ENNReal.ofReal (1 / 2) := by simp only [one_div, zero_lt_two, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
        rw [this, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal

        repeat rw [Domain.dist_eq]
        change idist _ _ ≤ unitInterval.half * idist _ _

        unfold for_seq_F
        apply le_trans (Domain.choice_lipschitz_left.to_idist_le _ _)
        erw [one_mul, Domain.seq'_assoc, Domain.seq'_assoc]

        obtain ⟨f, hf⟩ : ∃ f, (q ⬰ guard ξ ς e) = Domain.branch f := by
          obtain ⟨f', hf'⟩ := guard.is_branch (ξ := ξ) (ς := ς) (e := e)
          apply Domain.seq'_is_branch_of_branch
          exact hf'

        rw [hf]
        apply Domain.seq'_branch_contracting_left

      theorem for_seq_F_contracting {ξ ς e q} : ContractingWith (1/2) (for_seq_F ξ ς e q) := by
        constructor
        · exact one_half_lt_one
        · intros p p'

          have : ENNReal.ofNNReal (1 / 2) = 1 / 2 := by norm_num
          rw [this]

          exact for_seq_F_nonexpansive p p'

      theorem for_seq_eq {out ξ ς e S n} :
          for_seq ξ ς e (Go.Statement.denotation out ξ ς S) n =
          (for_seq_F ξ ς e (Go.Statement.denotation out ξ ς S))^[n] (Domain.branch λ σ ↦ {.next σ { val := .pure .unit }}) := by
        induction n with
        | zero => rfl
        | succ n IH =>
          unfold for_seq
          rw [IH, Nat.add_comm, Function.iterate_add, Function.iterate_one]
          rfl

      theorem for_seq_cauchy (out : Channel) (ξ : List Channel) (ς : String → Option Channel) (e : Go.Expression Go.Typ) (S : List ComputableGo.Statement) :
          CauchySeq (for_seq ξ ς e (Go.Statement.denotation out ξ ς S)) := by
        let p₀ : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
          Domain.branch λ σ ↦ {.next σ { val := .pure .unit }}

        have edist_ne_top : edist p₀ (for_seq_F ξ ς e (Go.Statement.denotation out ξ ς S) p₀) ≠ ⊤ := by
          rw [Domain.edist_eq]
          exact ENNReal.ofReal_ne_top

        obtain ⟨q, -, tendsto_nhds, -⟩ := for_seq_F_contracting.exists_fixedPoint p₀ edist_ne_top
        conv at tendsto_nhds => enter [1, n]; rw [← for_seq_eq]
        exact Filter.Tendsto.cauchySeq tendsto_nhds

      theorem for_seq_cauchy' (out : Channel) (ξ : List Channel) (ς : String → Option Channel) (e : Go.Expression Go.Typ) (S : List ComputableGo.Statement) :
          ∃ p, Filter.lim (Filter.atTop.map (for_seq ξ ς e (Go.Statement.denotation out ξ ς S))) = p := by
        apply Exists.imp
        · intros p
          apply Filter.Tendsto.limUnder_eq
        · apply cauchySeq_tendsto_of_complete
          apply for_seq_cauchy out
  end Go.Statement
end

end
