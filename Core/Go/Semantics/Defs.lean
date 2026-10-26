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
    (f : (n : ℕ) → (Fin n →ᵤ (Value.𝕍 Store.type Channel Address Go.Typ).type) → α) :
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
      apply Domain.bind_branch' (K := 1)
      · rfl
      · apply LipschitzWith.of_idist_le
        intros v₁ v₂
        rw [UniformFun.idist_eq_iSup]
        admit
      ·
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
      | .skip :: ss => Go.Statement.denotation out ξ ς ss ⬰ Domain.branch λ σ ↦ {.next σ ⟨Domain.pure .unit⟩}
      | .expr e :: ss => Go.Statement.denotation out ξ ς ss ⬰ ((λ _ ↦ .unit) <$> Go.Expression.denotation ξ ς e)
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
          | [] => .branch λ σ ↦ {.next σ { val := .abort }} -- empty call stack
        | _ => .branch λ σ ↦ {.next σ { val := .abort }} -- some statements after a `return`
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
      | .var x τ :: ss =>
        Go.Statement.denotation out ξ ς ss ⬰ Domain.branch λ σ ↦
        if ∃ h : (Store.type.ϙ σ).length > 0, (Store.type.ϙ σ)[(Store.type.ϙ σ).length - 1] x matches .none then
          let ⟨σ', v⟩ := zero σ τ
          if let .some σ' := Store.newVar σ' x v.to𝕍 then
            {.next σ' ⟨Domain.pure .unit⟩}
          else
            {.next σ ⟨Domain.abort⟩}
        else
          {.next σ ⟨Domain.abort⟩}
      | .assign r e :: ss => sorry
      | .make c τ cap :: ss =>
        (cap.elim (Domain.pure <| Value.𝕍.int 0) (Go.Expression.denotation ξ ς)) >>= λ cap ↦
          integer cap (default := Domain.branch λ σ ↦ {.next σ ⟨Domain.abort⟩})
            (λ cap ↦
              if cap < 0 then
                Domain.branch λ σ ↦ {.next σ ⟨Domain.abort⟩}
              else if cap = 0 then
                let γc : Channel := Classical.epsilon λ γ ↦ (∀ c, ς c ≠ .some γ) ∧ γ ∉ ξ
                Go.Statement.denotation out ξ (Function.update ς c (.some γc)) ss ∖ γc
              else -- if cap > 0 then
                Go.Statement.denotation out ξ ς ss ⬰ Domain.branch λ σ ↦
                  let ⟨σ, array⟩ := zero σ (.array cap.toNat τ)
                  let addr₁ := Store.freshAddr σ
                  let σ := Store.insert σ addr₁ array.to𝕍
                  let addr₂ := Store.freshAddr σ
                  let σ := Store.insert σ addr₂ (Value.𝕍.bool false)
                  let addr₃ := Store.freshAddr σ
                  let σ := Store.insert σ addr₃ (Value.𝕍.int 0)
                  if let .some σ := Store.newVar σ c (Value.𝕍.chan addr₃ τ addr₁ addr₂) then
                    {.next σ ⟨Domain.pure .unit⟩}
                  else
                    {.next σ ⟨Domain.abort⟩}
            )
      | .send c e :: ss =>
        let async : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
          Go.Expression.denotation ξ ς e >>= λ v ↦
          Go.Expression.denotation ξ ς c >>= λ c ↦
          Domain.branch λ σ ↦
            channel c (default := {.next σ { val := .abort }})
              (λ len' τ buf closed? ↦
                match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                | .none => {.next σ { val := .abort }}
                | .some (closed?, len, buf') =>
                  boolean closed? (default := {.next σ { val := .abort }})
                    λ closed? ↦ integer len (default := {.next σ { val := .abort }})
                    λ len ↦ array buf' (default := {.next σ { val := .abort }})
                    λ cap indices ↦
                      if h : closed? ∧ len ≥ 0 ∧ len < cap then
                        let i : Fin cap := ⟨len.toNat, propext (Int.toNat_lt h.2.1) ▸ h.2.2⟩
                        let σ' := Store.update σ buf (Value.𝕍.array cap (Function.update indices i v)) |>.bind λ σ ↦ Store.update σ len' (Value.𝕍.int <| len + 1)
                        match σ' with
                        | .some σ' => {.next σ' { val := .pure .unit }}
                        | .none => {.next σ { val := .abort }}
                      else if closed? ∧ len ≥ cap then
                        ∅
                      else
                        {.next σ { val := .abort }}
              )

        Go.Statement.denotation out ξ ς ss ⬰ if let .var x := c then
          if let .some c := ς x then
            -- Synchronous case
            Go.Expression.denotation ξ ς e >>= λ v ↦
            Domain.branch λ σ ↦
            if h : Value.𝕍_isSend v then
              {.send c (Value.𝕍_extract v h) ⟨Domain.pure .unit⟩}
            else
              {.next σ ⟨Domain.abort⟩}
          else
            -- Asynchronous case
            async
        else
          -- Asynchronous case
          async
      | .receive c r ok :: ss => sorry
      | .close c :: ss =>
        let async : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
          Go.Expression.denotation ξ ς c >>= λ c ↦
          Domain.branch λ σ ↦
            channel c (default := {.next σ { val := .abort }})
              (λ len' τ buf closed? ↦
                match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                | .none => {.next σ { val := .abort }}
                | .some (closed?', len, buf) =>
                  boolean closed?' (default := {.next σ { val := .abort }})
                    λ closed?' ↦ integer len (default := {.next σ { val := .abort }})
                    λ len ↦ array buf (default := {.next σ { val := .abort }})
                    λ cap indices ↦
                      if h : ¬closed?' ∧ cap > 0 then
                        match Store.update σ closed? (Value.𝕍.bool true) with
                        | .some σ' => {.next σ' { val := .pure .unit }}
                        | .none => {.next σ { val := .abort }}
                      else -- if closed? ∨ cap = 0 then
                        {.next σ { val := .abort }}
              )

        Go.Statement.denotation out ξ ς ss ⬰ if let .var x := c then
          if let .some c := ς x then
            -- Synchronous case
            Domain.branch λ σ ↦ {.close c ⟨Domain.pure .unit⟩}
          else
            -- Asynchronous case
            async
        else
          -- Asynchronous case
          async
      | .switch e «cases» defaul :: ss => sorry
      | .select «cases» defaul :: ss => sorry

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
