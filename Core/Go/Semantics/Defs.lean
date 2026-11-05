module

public import Core.Go.Semantics.Domains
public import Core.Go.Semantics.Operations
public import Core.Go.Syntax
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Extra.List

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

  def tuple {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α)
    (tup : List (Value.𝕍 Store.type Channel Address Go.Typ).type → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      tup
      v

  def struct {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α)
    (struct : (String →ᵤ Option (Value.𝕍 Store.type Channel Address Go.Typ).type) → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      struct
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      v

  def func {α} (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (default : α)
    (fn : (List Address × List Channel → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit) → α) :
      α :=
    Value.𝕍.casesOn (motive := λ _ ↦ α)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ _ _ _ ↦ default)
      (λ _ ↦ default)
      (λ _ _ ↦ default)
      (λ _ _ ↦ default)
      fn
      (λ _ ↦ default)
      v

  def Domain.branches {α β Γ «Σ»} [IMetricSpace β] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [CompleteSpace «Σ»] [CompleteSpace Γ] [CompleteSpace α] [CompleteSpace β]
    (p : Domain «Σ» Γ α β) (σ : «Σ») :
      Option (Set (Branch «Σ» Γ α (Domain «Σ» Γ α β))) :=
    match isSolution p with
    | .inl _ | .inr (.inl _) => .none
    | .inr (.inr f) => .some <| f σ

  /-! # The main semantics -/

  open Classical


  namespace Go
    -- TODO: what do we do of the cases where the type does not describe something that is sendable?
    def zero : Go.Typ → Value.Send𝕍 Address Go.Typ
      | .bool => .bool false
      | .int => .int 0
      | .str => .str ""
      | .map _ _ => .map [] true
      | .chan τ => .chan nil τ nil nil
      | .slice τ => .slice 0 0 0 nil
      | .array n τ => .array n λ i ↦ zero τ
      | .struct fs => .struct <| fs.attach.map λ ⟨⟨x, τ⟩, _⟩ ↦
        have _termination : sizeOf τ < sizeOf fs := by
          calc
            _ < sizeOf (x, τ) := by decreasing_trivial
            _ < _ := by decreasing_trivial

        ⟨x, zero τ⟩
      | .func _ _ => sorry
      | .named _ _ => sorry
      | .var _ => sorry
    termination_by τ => sizeOf τ

    instance : HasDefaultInit Store.type Channel (Value.Send𝕍 Address Go.Typ) where
      zero c σ := (σ, zero (Prod.snd c))

    /-- Value equality, for comparable values. -/
    inductive Value.𝕍.Eq : (Value.𝕍 Store.type Channel Address Go.Typ).type → (Value.𝕍 Store.type Channel Address Go.Typ).type → Prop
      | int {n : ℤ} : Value.𝕍.Eq (Value.𝕍.int n) (Value.𝕍.int n)
      | str {s : String} : Value.𝕍.Eq (Value.𝕍.str s) (Value.𝕍.str s)
      | bool {b : Bool} : Value.𝕍.Eq (Value.𝕍.bool b) (Value.𝕍.bool b)
      | chan {l τ r b} : Value.𝕍.Eq (Value.𝕍.chan l τ r b) (Value.𝕍.chan l τ r b)
      | struct {fs fs'} : (∀ x, (fs x).isSome ↔ (fs' x).isSome) → (∀ x v v', x ≠ "_" → fs x = .some v → fs' x = .some v' → Value.𝕍.Eq v v') → Value.𝕍.Eq (Value.𝕍.struct fs) (Value.𝕍.struct fs')
      | array {len f f'} : (∀ i : Fin len, Value.𝕍.Eq (f i) (f' i)) → Value.𝕍.Eq (Value.𝕍.array len f) (Value.𝕍.array len f')
      | slice {c c' l l' h h'} : Value.𝕍.Eq (Value.𝕍.slice c l h nil) (Value.𝕍.slice c' l' h' nil)
      | map : Value.𝕍.Eq (Value.𝕍.map (λ _ ↦ .none) true) (Value.𝕍.map (λ _ ↦ .none) true)
      -- `λ _ ↦ Domain.abort` cannot be obtained from the semantics alone, see below
      | func : Value.𝕍.Eq (Value.𝕍.func λ _ ↦ Domain.abort) (Value.𝕍.func λ _ ↦ Domain.abort)

    /-- Value disequality, for comparable values. -/
    inductive Value.𝕍.DisEq : (Value.𝕍 Store.type Channel Address Go.Typ).type → (Value.𝕍 Store.type Channel Address Go.Typ).type → Prop
      | int {n₁ n₂ : ℤ} : n₁ ≠ n₂ → Value.𝕍.DisEq (Value.𝕍.int n₁) (Value.𝕍.int n₂)
      | str {s₁ s₂ : String} : s₁ ≠ s₂ → Value.𝕍.DisEq (Value.𝕍.str s₁) (Value.𝕍.str s₂)
      | bool {b₁ b₂ : Bool} : b₁ ≠ b₂ → Value.𝕍.DisEq (Value.𝕍.bool b₁) (Value.𝕍.bool b₂)
      | chan {l l' τ r r' b b'} : r ≠ r' → Value.𝕍.DisEq (Value.𝕍.chan l τ r b) (Value.𝕍.chan l' τ r' b')
      | struct {fs fs' x v v'} : (∀ x, (fs x).isSome ↔ (fs' x).isSome) → x ≠ "_" → fs x = .some v → fs' x = .some v' → Value.𝕍.DisEq v v' → Value.𝕍.DisEq (Value.𝕍.struct fs) (Value.𝕍.struct fs')
      | array {len f f' i} : Value.𝕍.DisEq (f i) (f' i) → Value.𝕍.DisEq (Value.𝕍.array len f) (Value.𝕍.array len f')
      | slice {c c' l l' h h' r r'} : (r = nil ↔ r' ≠ nil) → Value.𝕍.DisEq (Value.𝕍.slice c l h r) (Value.𝕍.slice c' l' h' r')
      | map {f f' b b'} : (b = ¬b') → Value.𝕍.DisEq (Value.𝕍.map f b) (Value.𝕍.map f' b')
      | func {f f'} : (f = (λ _ ↦ Domain.abort) ↔ f' ≠ (λ _ ↦ Domain.abort)) → Value.𝕍.DisEq (Value.𝕍.func f) (Value.𝕍.func f')

    -- termination metric: depth addr@σ - List.length idx (depth addr@σ is finite from well-formedness of σ)
    mutual
      partial def updateRef (addr : Address) (v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (idx : List ((Value.𝕍 Store.type Channel Address Go.Typ).type ⊕ String))
        (σ : Store.type) :
          Option Store.type :=
        match idx with
        | [] => Store.update σ addr v
        | .inr r :: idx => do
          let v' ← Store.deref σ addr
          let ⟨σ', v'⟩ ← updateVal v' v (.inr r :: idx) σ
          Store.update σ' addr v'
        | .inl v'' :: idx => do
          let v' ← Store.deref σ addr
          Value.𝕍.casesOn (motive := λ _ ↦ Option Store.type)
            (λ _ ↦ .none) (λ _ ↦ .none) (λ _ ↦ .none)
            (λ _ low high buf ↦
              integer v'' (default := .none) λ v''' ↦ do
                guard (0 ≤ v''' ∧ v''' < high - low)
                updateRef buf v (.inl v'' :: idx) σ
            )
            (λ _ _ _ _ ↦ .none) (λ _ ↦ .none)
            (λ len _ ↦
              integer v'' (default := .none) λ v''' ↦ do
                guard (0 ≤ v''' ∧ v''' < len)
                let ⟨σ, v_⟩ ← updateVal v' v (.inl v'' :: idx) σ
                Store.update σ addr v_
            )
            (λ map isNil ↦ do
              guard (¬isNil ∧ idx.isEmpty)
              match map v'' with
              | .some addr => updateRef addr v idx σ
              | .none =>
                let addr' := Store.freshAddr σ
                Store.insert (← Store.insert σ addr' v) addr (Value.𝕍.map (Function.update map v'' addr') isNil)
            )
            (λ _ ↦ .none) (λ _ ↦ .none)
            v'

      partial def updateVal (v' v : (Value.𝕍 Store.type Channel Address Go.Typ).type) (idx : List ((Value.𝕍 Store.type Channel Address Go.Typ).type ⊕ String))
        (σ : Store.type) :
          Option (Store.type × (Value.𝕍 Store.type Channel Address Go.Typ).type) :=
        match idx with
        | [] => .some (σ, v)
        | .inr name :: idx =>
          struct v' (default := .none) λ fs ↦ do
            let v'' ← fs name
            let ⟨σ, v''⟩ ← updateVal v'' v idx σ
            pure ⟨σ, Value.𝕍.struct (Function.update fs name v'')⟩
        | .inl e :: idx =>
          Value.𝕍.casesOn (motive := λ _ ↦ Option (Store.type × (Value.𝕍 Store.type Channel Address Go.Typ).type))
            (λ _ ↦ .none) (λ _ ↦ .none) (λ _ ↦ .none)
            (λ cap low high buf ↦
              integer e (default := .none) (λ e' ↦ do
                guard (0 ≤ e' ∧ e' < high - low)
                let σ ← updateRef buf v (.inl e :: idx) σ
                pure (σ, Value.𝕍.slice cap low high buf)
            ))
            (λ _ _ _ _ ↦ .none) (λ _ ↦ .none)
            (λ len indices ↦
              integer e (default := .none) (λ e' ↦ do
                if h : 0 ≤ e' ∧ e' < len then
                  let i : Fin len := ⟨e'.toNat, propext (Int.toNat_lt h.1) ▸ h.2⟩
                  let ⟨σ, v''⟩ ← updateVal (indices i) v idx σ
                  pure ⟨σ, Value.𝕍.array len (Function.update indices i v'')⟩
                else
                  .none
            ))
            (λ fs isNil ↦ do
              guard (¬isNil ∧ idx = [])
              if let .some addr := fs e then
                let σ ← updateRef addr v [] σ
                pure ⟨σ, Value.𝕍.map fs isNil⟩
              else
                let addr := Store.freshAddr σ
                pure ⟨Store.insert σ addr v, Value.𝕍.map (Function.update fs e addr) isNil⟩
            )
            (λ _ ↦ .none) (λ _ ↦ .none)
            v'
    end

    def updateRefs (addrs : List Address) (vs : List (Value.𝕍 Store.type Channel Address Go.Typ).type) (idxs : List (List ((Value.𝕍 Store.type Channel Address Go.Typ).type ⊕ String)))
        (σ : Store.type) :
          Option Store.type :=
      List.zip₃ addrs vs idxs |>.foldlM (init := σ) λ σ ⟨addr, v, idx⟩ ↦ updateRef addr v idx σ

    def deref (σ : Store.type) (addr : Address) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type :=
      match Store.deref σ addr with
      | .some v => .pure v
      | .none => .abort

    def guard (pol : Bool) (v : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
      v >>= λ v ↦ Domain.branch λ σ ↦
        boolean v (default := {.next σ ⟨.abort⟩})
          λ b ↦ if b = pol then {.next σ ⟨.pure .unit⟩} else ∅

    def for_seq_F (e : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type)
      (P' P : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit) :
        Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
      (P ⬰ P' ⬰ guard true e) ⊻ (.pure .unit ⬰ guard false e)

    def for_seq (e : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type)
      (P : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit) :
        ℕ → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit
      | 0 => .branch λ σ ↦ {.next σ ⟨.pure .unit⟩}
      | i + 1 => for_seq_F e P (for_seq e P i)

    variable (out : Channel)

    mutual
      protected def Expression.denotation (ξ : List Channel) (ς : String → Option Channel) :
          Go.Expression Go.Typ → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Value.𝕍 Store.type Channel Address Go.Typ).type
        | .nat n => Domain.pure (Value.𝕍.int n.toInt!)
        | .str s => Domain.pure (Value.𝕍.str s)
        | .true => Domain.pure (Value.𝕍.bool true)
        | .false => Domain.pure (Value.𝕍.bool false)
        | .var x => Domain.branch λ σ ↦
          if let .some v := do Store.deref σ (← Store.addrOf σ x) then
            {.next σ ⟨.pure v⟩}
          else
            {.next σ ⟨.abort⟩}
        | .unary op e =>
          sorry
        | .binary op e₁ e₂ =>
          sorry
        | .index e₁ e₂ =>
          sorry
        | .field e x =>
          Go.Expression.denotation ξ ς e >>= λ v ↦ struct v (default := Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}) λ fs ↦
            if let .some v := fs x then
              Domain.branch λ σ ↦ {.next σ ⟨.pure v⟩}
            else
              Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}
        | .call f es =>
          Go.Expression.denotation ξ ς f >>= λ f ↦
          func f (default := Domain.branch λ σ ↦ {.next σ ⟨Domain.abort⟩}) λ f ↦
            Go.Expression.denotations ξ ς es >>= λ vs ↦
            let γret := Classical.epsilon λ γ ↦ γ ∉ ξ ∧ (∀ c, ς c ≠ γ)
            Domain.branch λ σ ↦
              let (addrs, σ') := vs.foldl (init := ([], σ)) λ (addrs, σ) v ↦
                let addr := Store.freshAddr σ
                (addrs ++ [addr], Store.insert σ addr v)
              {.next σ' ⟨
                Prod.snd <$> (f (addrs, γret :: ξ) ∥ Domain.branch λ σ ↦ {.recv γret λ v ok ↦ ⟨.pure v.to𝕍⟩}) ∖ γret
              ⟩}
        | .builtin f es =>
          sorry
        | .structLit τ es' =>
          let (eq := h) (xs, es) := es'.unzip

          have _termination : sizeOf es ≤ sizeOf es' := by
            grind only [!List.sizeOf_unzip_snd_le]

          Go.Expression.denotations ξ ς es >>= λ vs ↦
          Domain.branch λ σ ↦
            {.next σ ⟨.pure (Value.𝕍.struct (List.lookup · (xs.zip vs)))⟩}
        | .sliceLit τ es =>
          Go.Expression.denotations ξ ς es >>= λ vs ↦
          let arr := Value.𝕍.array _ (List.get vs)
          Domain.branch λ σ ↦
            let addr := Store.freshAddr σ
            let σ' := Store.insert σ addr arr
            {.next σ' ⟨.pure (Value.𝕍.slice vs.length 0 vs.length addr)⟩}
        | .mapLit τ es' =>
          let (eq := h) (ks, es) := es'.unzip

          have _termination₁ : sizeOf ks ≤ sizeOf es' := by
            grind only [!List.sizeOf_unzip_fst_le]
          have _termination₂ : sizeOf es ≤ sizeOf es' := by
            grind only [!List.sizeOf_unzip_snd_le]

          -- NOTE: Evaluation order between the keys and values is not specified (<https://go.dev/ref/spec#Order_of_evaluation>);
          -- here we evaluate all keys before the values
          Go.Expression.denotations ξ ς ks >>= λ ks ↦
          Go.Expression.denotations ξ ς es >>= λ vs ↦
          Domain.branch λ σ ↦
            let (addrs, σ') := vs.foldl (init := ([], σ)) λ (addrs, σ) v ↦
              let addr := Store.freshAddr σ
              (addrs ++ [addr], Store.insert σ addr v)
            {.next σ' ⟨.pure (Value.𝕍.map (List.lookup · (ks.zip addrs)) false)⟩}
        | .make τ es =>
          sorry
        | .funcLit params _ body => Domain.pure <| Value.𝕍.func λ ⟨hs, ξ⟩ ↦
          Domain.branch λ σ ↦
            if hs.length = params.length then
              if let .some σ' := params.zip hs |>.foldlM (init := σ) λ σ ⟨(p, _), h⟩ ↦ Store.register σ p h then
                {.next σ' ⟨Go.Statement.denotation ξ (λ _ ↦ .none) body⟩}
              else
                {.next σ ⟨.abort⟩}
            else
              {.next σ ⟨.abort⟩}
      termination_by e => sizeOf e

      protected def Expression.denotations (ξ : List Channel) (ς : String → Option Channel) :
          List (Go.Expression Go.Typ) → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (List (Value.𝕍 Store.type Channel Address Go.Typ).type)
        | [] => .pure []
        | e :: es => Go.Expression.denotation ξ ς e >>= λ v ↦ (v :: ·) <$> Go.Expression.denotations ξ ς es
      termination_by es => sizeOf es

      def evalRef (ξ : List Channel) (ς : String → Option Channel) :
          Ref (Expression Typ) → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (Option Address × List ((Value.𝕍 Store.type Channel Address Go.Typ).type ⊕ String))
        | .wildcard => Domain.branch λ σ ↦ {.next σ ⟨Domain.pure (.none, [])⟩}
        | .var x => Domain.branch λ σ ↦ if let .some addr := Store.addrOf σ x then {.next σ ⟨Domain.pure (.some addr, [])⟩} else {.next σ ⟨Domain.abort⟩}
        | .field r name => evalRef ξ ς r >>= λ ⟨addr, args⟩ ↦ Domain.pure ⟨addr, args ++ [.inr name]⟩
        | .index r e => evalRef ξ ς r >>= λ ⟨addr, args⟩ ↦ Go.Expression.denotation ξ ς e >>= λ v ↦ Domain.pure ⟨addr, args ++ [.inl v]⟩
      termination_by r => sizeOf r

      def evalRefs (ξ : List Channel) (ς : String → Option Channel) :
          List (Ref (Expression Typ)) → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) (List (Option Address × List ((Value.𝕍 Store.type Channel Address Go.Typ).type ⊕ String)))
        | [] => Domain.pure []
        | r :: rs =>
          evalRef ξ ς r >>= λ r ↦
          evalRefs ξ ς rs >>= λ rs ↦
          Domain.pure (r :: rs)
      termination_by rs => sizeOf rs

      protected def Statement.denotation (ξ : List Channel) (ς : String → Option Channel) :
          List ComputableGo.Statement → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit
        | [] => .branch λ σ ↦ {.next σ ⟨.pure .unit⟩}
        | .skip :: ss => Go.Statement.denotation ξ ς ss ⬰ Domain.branch λ σ ↦ {.next σ ⟨.pure .unit⟩}
        | .expr e :: ss => Go.Statement.denotation ξ ς ss ⬰ ((λ _ ↦ .unit) <$> Go.Expression.denotation ξ ς e)
        | .panic e :: ss => Go.Statement.denotation ξ ς ss ⬰ (Go.Expression.denotation ξ ς e >>= λ _ ↦ Domain.abort)
        | .return es :: ss => match ss with
          | [] => match ξ with
            | ret :: _ => Go.Expression.denotations ξ ς es >>= λ vs ↦ Domain.branch λ σ ↦ match Store.popϙ σ with
              | .none => {.next σ ⟨.abort⟩}
              | .some σ => {.next σ ⟨
                  if h₁ : vs.length = 1 then
                    if h₂ : Value.𝕍_isSend vs[0] then
                      Domain.branch λ _ ↦ {.send ret (Value.𝕍_extract vs[0] h₂) ⟨.pure .unit⟩}
                    else
                      .abort
                  else if h₂ : ∀ v ∈ vs, Value.𝕍_isSend v then
                    Domain.branch λ _ ↦ {.send ret (Value.𝕍_extract (Value.𝕍.tuple vs) (Value.𝕍_isSend.tuple h₂)) ⟨.pure .unit⟩}
                  else
                    Domain.abort
              ⟩}
            | [] => .branch λ σ ↦ {.next σ { val := .abort }} -- empty call stack
          | _ => .branch λ σ ↦ {.next σ { val := .abort }} -- some statements after a `return`
        | .print e :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ (Go.Expression.denotation ξ ς e >>= λ v ↦
            if h : Value.𝕍_isSend v then
              Domain.branch λ _ ↦ {.send out (Value.𝕍_extract v h) ⟨.pure .unit⟩}
            else
              Domain.abort)
        | .if e S₁ S₂ :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ (
              (Go.Statement.denotation ξ ς S₁ ⬰ guard true (Go.Expression.denotation ξ ς e))
            ⊻ (Go.Statement.denotation ξ ς S₂ ⬰ guard false (Go.Expression.denotation ξ ς e))
          )
        | .for e S :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ Filter.lim (Filter.atTop.map
            (for_seq (Go.Expression.denotation ξ ς e) (Go.Statement.denotation ξ ς S)))
        | .go S :: ss => (λ _ ↦ PUnit.unit) <$> (Go.Statement.denotation ξ ς S ∥ Go.Statement.denotation ξ ς ss)
        | .var x τ :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ Domain.branch λ σ ↦
          if ∃ h : (Store.type.ϙ σ).length > 0, (Store.type.ϙ σ)[(Store.type.ϙ σ).length - 1] x matches .none then
            let v := zero τ
            if let .some σ' := Store.newVar σ x v.to𝕍 then
              {.next σ' ⟨.pure .unit⟩}
            else
              {.next σ ⟨.abort⟩}
          else
            {.next σ ⟨.abort⟩}
        | .assign rs es :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ (
            -- evaluate all references from left to right
            evalRefs ξ ς rs >>= λ rs ↦
            -- then evaluate all values from left to right
            Go.Expression.denotations ξ ς es >>= λ vs ↦
            if h₁ : vs.length = 0 then
              Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}
            else if h₂ : vs.length = 1 then
              -- if a single value, check the length of the returned tuple and assign each component to the references
              if h₃ : rs.length = 0 then
                Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}
              else if h₄ : rs.length = 1 then
                -- if a single reference, assign directly (no tuple)
                tuple vs[0] (default := Domain.branch λ σ ↦
                  if let ⟨.some addr, args⟩ := rs[0] then
                    if let .some σ' := updateRef addr vs[0] args σ then
                      {.next σ' ⟨.pure .unit⟩}
                    else
                      {.next σ ⟨.abort⟩}
                  else
                    {.next σ ⟨.pure .unit⟩}
                )
                  (λ _ ↦ Domain.branch λ σ ↦ {.next σ ⟨.abort⟩})
              else
                -- otherwise assign each component of the tuple to the corresponding reference
                tuple vs[0] (default := Domain.branch λ σ ↦ {.next σ ⟨.abort⟩})
                  (λ vs ↦ Domain.branch λ σ ↦ if h₅ : vs.length = rs.length then
                      let ⟨addrs, idxs, vss⟩ := rs.zip vs |>.filterMap (λ ⟨⟨addr, idx⟩, v⟩ ↦ (·, idx, v) <$> addr) |>.unzip₃
                      if let .some σ' := updateRefs addrs vss idxs σ then
                        {.next σ' ⟨.pure .unit⟩}
                      else
                        {.next σ ⟨.abort⟩}
                    else
                      {.next σ ⟨.abort⟩}
                  )
            else
              -- otherwise, check that all values are not tuples, that there are enough values, and assign to the references
              Domain.branch λ σ ↦ if h_nottup : ∀ v ∈ vs, tuple v (default := True) (λ _ ↦ False) then
                if h₅ : vs.length = rs.length then
                  let ⟨addrs, idxs, vss⟩ := rs.zip vs |>.filterMap (λ ⟨⟨addr, idx⟩, v⟩ ↦ (·, idx, v) <$> addr) |>.unzip₃
                  if let .some σ' := updateRefs addrs vss idxs σ then
                    {.next σ' ⟨.pure .unit⟩}
                  else
                    {.next σ ⟨.abort⟩}
                else
                  {.next σ ⟨.abort⟩}
              else
                {.next σ ⟨.abort⟩}
          )
        | .make c τ cap :: ss =>
          (cap.attach.elim (.pure <| Value.𝕍.int 0) (λ ⟨e, _⟩ ↦ Go.Expression.denotation ξ ς e)) >>= λ cap ↦
            integer cap (default := Domain.branch λ σ ↦ {.next σ ⟨.abort⟩})
              (λ cap ↦
                if cap < 0 then
                  Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}
                else if cap = 0 then
                  let γc : Channel := Classical.epsilon λ γ ↦ (∀ c, ς c ≠ .some γ) ∧ γ ∉ ξ
                  Go.Statement.denotation ξ (Function.update ς c (.some γc)) ss ∖ γc
                else -- if cap > 0 then
                  Go.Statement.denotation ξ ς ss ⬰ Domain.branch λ σ ↦
                    let array := zero (.array cap.toNat τ)
                    let addr₁ := Store.freshAddr σ
                    let σ := Store.insert σ addr₁ array.to𝕍
                    let addr₂ := Store.freshAddr σ
                    let σ := Store.insert σ addr₂ (Value.𝕍.bool false)
                    let addr₃ := Store.freshAddr σ
                    let σ := Store.insert σ addr₃ (Value.𝕍.int 0)
                    if let .some σ := Store.newVar σ c (Value.𝕍.chan addr₃ τ addr₁ addr₂) then
                      {.next σ ⟨.pure .unit⟩}
                    else
                      {.next σ ⟨.abort⟩}
              )
        | .send c e :: ss =>
          let async : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
            Go.Expression.denotation ξ ς e >>= λ v ↦
            Go.Expression.denotation ξ ς c >>= λ c ↦
            Domain.branch λ σ ↦
              channel c (default := {.next σ ⟨.abort⟩})
                (λ len' τ buf closed? ↦
                  match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                  | .none => {.next σ ⟨.abort⟩}
                  | .some (closed?, len, buf') =>
                    boolean closed? (default := {.next σ ⟨.abort⟩})
                      λ closed? ↦ integer len (default := {.next σ ⟨.abort⟩})
                      λ len ↦ array buf' (default := {.next σ ⟨.abort⟩})
                      λ cap indices ↦
                        if h : closed? ∧ len ≥ 0 ∧ len < cap then
                          let i : Fin cap := ⟨len.toNat, propext (Int.toNat_lt h.2.1) ▸ h.2.2⟩
                          let σ' := Store.update σ buf (Value.𝕍.array cap (Function.update indices i v)) |>.bind λ σ ↦ Store.update σ len' (Value.𝕍.int <| len + 1)
                          match σ' with
                          | .some σ' => {.next σ' ⟨.pure .unit⟩}
                          | .none => {.next σ ⟨.abort⟩}
                        else if closed? ∧ len ≥ cap then
                          ∅
                        else
                          {.next σ ⟨.abort⟩}
                )

          Go.Statement.denotation ξ ς ss ⬰ if let .var x := c then
            if let .some c := ς x then
              -- Synchronous case
              Go.Expression.denotation ξ ς e >>= λ v ↦
              Domain.branch λ σ ↦
              if h : Value.𝕍_isSend v then
                {.send c (Value.𝕍_extract v h) ⟨.pure .unit⟩}
              else
                {.next σ ⟨.abort⟩}
            else
              -- Asynchronous case
              async
          else
            -- Asynchronous case
            async
        | .receive c r ok :: ss =>
          Go.Statement.denotation ξ ς ss ⬰ (
            evalRef ξ ς r >>= λ (addrᵣ, argsᵣ) ↦
            ok.attach.elim (Domain.pure (Option.none, [])) (λ ⟨r, _⟩ ↦ evalRef ξ ς r) >>= λ (addrₒₖ, argsₒₖ) ↦
            let upd (vₓ vₒₖ : (Value.𝕍 Store.type Channel Address Go.Typ).type) : Store.type → Option Store.type :=
              addrₒₖ.elim .some (updateRef · vₒₖ argsₒₖ) <=< addrᵣ.elim .some (updateRef · vₓ argsᵣ)

            let async : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
              Go.Expression.denotation ξ ς c >>= λ c ↦
              Domain.branch λ σ ↦
                channel c (default := {.next σ ⟨.abort⟩})
                (λ len' τ buf closed? ↦
                  match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                  | .none => {.next σ ⟨.abort⟩}
                  | .some (closed?', len, buf') =>
                    boolean closed?' (default := {.next σ ⟨.abort⟩})
                      λ closed?' ↦ integer len (default := {.next σ ⟨.abort⟩})
                      λ len ↦ array buf' (default := {.next σ ⟨.abort⟩})
                      λ cap indices ↦
                        if h : cap > 0 ∧ len > 0 then -- memory well-formedness could give that len ≤ cap?
                          -- NOTE: there are messages to be received still
                          let v₀ := indices ⟨0, h.1⟩
                          let σ' := do
                            let σ ← Store.update σ buf (Value.𝕍.array cap λ i ↦ if h : i = cap - 1 then indices ⟨cap - 1, by grind only⟩ else indices ⟨i + 1, by grind only⟩)
                            let σ ← Store.update σ len' (Value.𝕍.int (len - 1))
                            upd v₀ (Value.𝕍.bool true) σ
                          if let .some σ' := σ' then
                            {.next σ' ⟨.pure .unit⟩}
                          else
                            {.next σ ⟨.abort⟩}
                        else if len = 0 ∧ ¬closed?' then
                          -- NOTE: no message to receive, but channel not closed so wait
                          ∅
                        else if len = 0 ∧ closed?' then
                          -- NOTE: channel closed, no more messages to receive
                          let v := Go.zero τ
                          if let .some σ' := upd v.to𝕍 (Value.𝕍.bool false) σ then
                            {.next σ' ⟨.pure .unit⟩}
                          else
                            {.next σ ⟨.abort⟩}
                        else
                          {.next σ ⟨.abort⟩}
                )

            if let .var x := c then
              if let .some c := ς x then
                -- Synchronous case
                Domain.branch λ σ ↦ {
                  .recv c λ v ok ↦ ⟨Domain.branch λ σ ↦ {
                      if let .some σ := upd v.to𝕍 (Value.𝕍.bool ok) σ then
                        .next σ ⟨.pure .unit⟩
                      else
                        .next σ ⟨.abort⟩
                    }⟩
                }
              else
                -- Asynchronous case
                async
            else
              -- Asynchronous case
              async
          )
        | .close c :: ss =>
          let async : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
            Go.Expression.denotation ξ ς c >>= λ c ↦
            Domain.branch λ σ ↦
              channel c (default := {.next σ ⟨.abort⟩})
                (λ len' τ buf closed? ↦
                  match (Store.deref σ closed?).bind λ closed? ↦ (Store.deref σ len').bind λ len ↦ (Store.deref σ buf).bind λ buf ↦ pure (closed?, len, buf) with
                  | .none => {.next σ ⟨.abort⟩}
                  | .some (closed?', len, buf) =>
                    boolean closed?' (default := {.next σ ⟨.abort⟩})
                      λ closed?' ↦ integer len (default := {.next σ ⟨.abort⟩})
                      λ len ↦ array buf (default := {.next σ ⟨.abort⟩})
                      λ cap indices ↦
                        if h : ¬closed?' ∧ cap > 0 then
                          match Store.update σ closed? (Value.𝕍.bool true) with
                          | .some σ' => {.next σ' ⟨.pure .unit⟩}
                          | .none => {.next σ ⟨.abort⟩}
                        else -- if closed? ∨ cap = 0 then
                          {.next σ ⟨.abort⟩}
                )

          Go.Statement.denotation ξ ς ss ⬰ if let .var x := c then
            if let .some c := ς x then
              -- Synchronous case
              Domain.branch λ σ ↦ {.close c ⟨.pure .unit⟩}
            else
              -- Asynchronous case
              async
          else
            -- Asynchronous case
            async
        | .switch e «cases» defaul :: ss =>
          Go.Expression.denotation ξ ς e >>= λ v ↦

          let p₀ := Go.Statement.denotation ξ ς defaul
          let rec go : List (SwitchClause (Expression Typ) ComputableGo.Statement) → Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit
            | [] => p₀
            | ⟨head, body⟩ :: cs =>
              Go.Expression.denotation ξ ς head >>= λ v' ↦
              if Value.𝕍.Eq v v' then
                Go.Statement.denotation ξ ς body
              else if Value.𝕍.DisEq v v' then
                go cs
              else
                Domain.branch λ σ ↦ {.next σ ⟨.abort⟩}
          termination_by cs => sizeOf cs

          Go.Statement.denotation ξ ς ss ⬰ go «cases»
        | .select «cases» defaul :: ss =>
          let case_denotation (c : SelectClause ComputableGo.Statement) (_h : c ∈ «cases») : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
            have _termination : 1 + sizeOf c.guard + sizeOf c.body < 1 + (1 + sizeOf «cases» + sizeOf defaul) + sizeOf ss := by
              calc
                _ = sizeOf c := by rfl
                _ < sizeOf «cases» := by decreasing_trivial
                _ < _ := by simp +arith only

            Go.Statement.denotation ξ ς (c.guard :: c.body)

          Go.Statement.denotation ξ ς ss ⬰ if h : «cases».length = 0 then
            match defaul with
            | .some defaul => Domain.branch λ σ ↦ {.next σ ⟨Go.Statement.denotation ξ ς defaul⟩}
            | .none => Domain.branch λ σ ↦ ∅
          else
            let p := «cases».tail.attach.foldl (init := case_denotation («cases».head (by grind only [=List.length_nil])) (List.head_mem _)) λ acc ⟨c, h⟩ ↦
              acc ⊻ case_denotation c (List.mem_of_mem_tail h)
            match defaul with
            | .some defaul =>
              Domain.branch λ σ ↦
                if let .some br := p.branches σ then
                  if br = ∅ then
                    {.next σ ⟨Go.Statement.denotation ξ ς defaul⟩}
                  else
                    ∅
                else
                  {.next σ ⟨Go.Statement.denotation ξ ς defaul⟩}
            | .none => p
      termination_by cs => sizeOf cs
    end

    variable {out}

    theorem guard.is_branch {e} : ∃ f, guard true e = Domain.branch f := by
      unfold guard
      apply Domain.bind_branch' (K := 1)
      · rfl
      · apply LipschitzWith.of_idist_le
        intros v₁ v₂
        erw [UniformFun.idist_eq_iSup, one_mul, Subtype.coe_le_coe]
        admit
      ·
        admit

    theorem for_seq_F_nonexpansive {e q} :
        ∀ p p', edist (for_seq_F e q p) (for_seq_F e q p') ≤ (1/2) * edist p p' := by
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

      obtain ⟨f, hf⟩ : ∃ f, (q ⬰ guard true e) = Domain.branch f := by
        obtain ⟨f', hf'⟩ := guard.is_branch (e := e)
        apply Domain.seq'_is_branch_of_branch
        exact hf'

      rw [hf]
      apply Domain.seq'_branch_contracting_left

    theorem for_seq_F_contracting {e q} : ContractingWith (1/2) (for_seq_F e q) := by
      constructor
      · exact one_half_lt_one
      · intros p p'

        have : ENNReal.ofNNReal (1 / 2) = 1 / 2 := by norm_num
        rw [this]

        exact for_seq_F_nonexpansive p p'

    theorem for_seq_eq {ξ ς e S n} :
        for_seq e (Go.Statement.denotation out ξ ς S) n =
        (for_seq_F e (Go.Statement.denotation out ξ ς S))^[n] (Domain.branch λ σ ↦ {.next σ ⟨.pure .unit⟩}) := by
      induction n with
      | zero => rfl
      | succ n IH =>
        unfold for_seq
        rw [IH, Nat.add_comm, Function.iterate_add, Function.iterate_one]
        rfl

    theorem for_seq_cauchy (ξ : List Channel) (ς : String → Option Channel) (e : _) (S : List ComputableGo.Statement) :
        CauchySeq (for_seq e (Go.Statement.denotation out ξ ς S)) := by
      let p₀ : Domain Store.type Channel (Value.Send𝕍 Address Go.Typ) PUnit :=
        Domain.branch λ σ ↦ {.next σ ⟨.pure .unit⟩}

      have edist_ne_top : edist p₀ (for_seq_F e (Go.Statement.denotation out ξ ς S) p₀) ≠ ⊤ := by
        rw [Domain.edist_eq]
        exact ENNReal.ofReal_ne_top

      obtain ⟨q, -, tendsto_nhds, -⟩ := for_seq_F_contracting.exists_fixedPoint p₀ edist_ne_top
      conv at tendsto_nhds => enter [1, n]; rw [← for_seq_eq]
      exact Filter.Tendsto.cauchySeq tendsto_nhds

    theorem for_seq_cauchy' (ξ : List Channel) (ς : String → Option Channel) (e : _) (S : List ComputableGo.Statement) :
        ∃ p, Filter.lim (Filter.atTop.map (for_seq e (Go.Statement.denotation out ξ ς S))) = p := by
      apply Exists.imp
      · intros p
        apply Filter.Tendsto.limUnder_eq
      · apply cauchySeq_tendsto_of_complete
        apply for_seq_cauchy
  end Go
end

end
