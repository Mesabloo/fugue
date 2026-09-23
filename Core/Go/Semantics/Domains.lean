module

meta import CustomPrelude
public import Extra.Nat
public import Extra.AList
import Extra.Fin
import Extra.List
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Maps.Basic
public import Extra.Topology.Constructions.SumProd
public import Extra.Topology.Constructions.Maps
public import Extra.Topology.IMetricSpace.Constructions
public import Extra.Topology.ClosedEmbedding
public import Extra.Topology.IsometricEmbedding
public import Extra.Topology.UniformContinuousMap
public import Extra.Topology.LipschitzMap
import Extra.Set
import Extra.Prop
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
-- import Mathlib.Data.Part

@[expose] public section

open scoped UniformConvergence
attribute [-instance] UniformFun.instPseudoEMetricSpace UniformFun.instEMetricSpace

lemma max_succ {m n} : (m + 1) ⊔ (n + 1) = (m ⊔ n) + 1 := by
  grind only [= max_def]

structure Object.{u} where
  carrier : Type u
  [MetricSpace : PseudoIMetricSpace carrier]

instance {o : Object} : PseudoIMetricSpace o.carrier := o.MetricSpace

noncomputable section Domain
  /-! # The semantics domains
  -/
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  def Branch :=
      (Γ × (α →ᵤ Bool →ᵤ Restriction γ unitInterval.half))
    ⊕ (Γ × α × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ («Σ» × Restriction γ unitInterval.half)

  section Branch
    variable {«Σ» Γ α β γ δ}

    @[match_pattern]
    protected abbrev Branch.recv (c : Γ) (π : α →ᵤ Bool →ᵤ Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := Sum.inl (c, π)
    @[match_pattern]
    protected abbrev Branch.send (c : Γ) (v : α) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inl (c, v, p))
    @[match_pattern]
    protected abbrev Branch.close (c : Γ) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inl (c, p)))
    @[match_pattern]
    protected abbrev Branch.sync (c : Γ) (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inl (c, p))))
    @[match_pattern]
    protected abbrev Branch.next (σ : «Σ») (p : Restriction γ unitInterval.half) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inr (σ, p))))

    @[cases_eliminator]
    def Branch.casesOn {motive : Branch «Σ» Γ α γ → Sort _}
      (recv : ∀ c π, motive (.recv c π))
      (send : ∀ c v p, motive (.send c v p))
      (close : ∀ c p, motive (.close c p))
      (sync : ∀ c p, motive (.sync c p))
      (next : ∀ σ p, motive (.next σ p)) :
        ∀ b, motive b
      | .recv c π => recv c π
      | .send c v p => send c v p
      | .close c p => close c p
      | .sync c p => sync c p
      | .next σ p => next σ p

    instance Branch.instPseudoIMetricSpace [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] :
        PseudoIMetricSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (PseudoIMetricSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    instance [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ]
      [IsUltrametricIDist «Σ»] [IsUltrametricIDist Γ] [IsUltrametricIDist α] [IsUltrametricIDist γ] :
        IsUltrametricIDist (Branch «Σ» Γ α γ) :=
      inferInstanceAs (IsUltrametricIDist (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    instance Branch.instIMetricSpace [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace γ] :
        IMetricSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (IMetricSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    instance Branch.instCompleteSpace [IMetricSpace «Σ»] [CompleteSpace «Σ»] [IMetricSpace Γ] [CompleteSpace Γ] [IMetricSpace α] [CompleteSpace α] [IMetricSpace γ] [CompleteSpace γ] :
        CompleteSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (CompleteSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))

    variable [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ]

    @[simp]
    theorem Branch.idist_recv_recv {c c' : Γ} {π π' : α →ᵤ Bool →ᵤ Restriction γ unitInterval.half} :
        idist (Branch.recv («Σ» := «Σ») c π) (Branch.recv c' π') = idist c c' ⊔ idist π π' :=
      rfl

    @[simp]
    theorem Branch.idist_send_send {c c' : Γ} {v v' : α} {p p' : Restriction γ unitInterval.half} :
        idist (Branch.send («Σ» := «Σ») c v p) (Branch.send c' v' p') = idist c c' ⊔ idist v v' ⊔ idist p p' := by
      rw [sup_assoc]
      rfl

    @[simp]
    theorem Branch.idist_sync_sync {c c' : Γ} {p p' : Restriction γ unitInterval.half} :
        idist (Branch.sync («Σ» := «Σ») (α := α) c p) (Branch.sync c' p') = idist c c' ⊔ idist p p' :=
      rfl

    @[simp]
    theorem Branch.idist_close_close {c c' : Γ} {p p' : Restriction γ unitInterval.half} :
        idist (Branch.close («Σ» := «Σ») (α := α) c p) (Branch.close c' p') = idist c c' ⊔ idist p p' :=
      rfl


    @[simp]
    theorem Branch.idist_next_next {σ σ' : «Σ»} {p p' : Restriction γ unitInterval.half} :
        idist (Branch.next (Γ := Γ) (α := α) σ p) (Branch.next σ' p') = idist σ σ' ⊔ idist p p' :=
      rfl
  end Branch

  variable [PseudoIMetricSpace β] [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit := .of_metric_space_of_dist_le_one
  instance (priority := high) : CompleteSpace PUnit := inferInstance
  instance : DiscreteIMetricSpace PUnit where

  def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  instance instUltrametricIDistIterativeDomain {n}
      [IsUltrametricIDist «Σ»] [IsUltrametricIDist Γ] [IsUltrametricIDist α] [IsUltrametricIDist β] :
        IsUltrametricIDist (IterativeDomain «Σ» Γ α β n).carrier :=
      match n with
      | 0 => inferInstanceAs (IsUltrametricIDist (β ⊕ PUnit))
      | n + 1 =>
        let : IsUltrametricIDist (IterativeDomain «Σ» Γ α β n).carrier := instUltrametricIDistIterativeDomain (n := n)
        inferInstanceAs (IsUltrametricIDist (β ⊕ PUnit ⊕ («Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier))))

  section
    variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

    theorem IterativeDomain.idist_cast {m n} (h : m = n) (p q : (IterativeDomain «Σ» Γ α β m).carrier) :
        idist p q = idist (h ▸ p) (h ▸ q) := by
      cases h
      rfl

    theorem IterativeDomain.idist_cast' {m n} (h : m = n) (f : ℕ → ℕ) (p q : (IterativeDomain «Σ» Γ α β (f m)).carrier) :
        idist p q = idist (h ▸ p) (h ▸ q) := by
      cases h
      rfl

    theorem IterativeDomain.Branch.idist_cast {m n} (h : m = n) (p q : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β m).carrier) :
        idist p q = idist (h ▸ p) (h ▸ q) := by
      cases h
      rfl

    @[match_pattern]
    def IterativeDomain.leaf {n} (v : β) : (IterativeDomain «Σ» Γ α β n).carrier := match n with
      | 0 | _ + 1 => .inl v

    @[simp]
    theorem IterativeDomain.idist_leaf_leaf {v v' : β} {n} :
        idist (IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := n) v) (IterativeDomain.leaf v') = idist v v' := by
      cases n <;> rfl

    @[push_cast]
    theorem IterativeDomain.leaf_cast {v : β} {m n} {h : m = n} :
        h ▸ IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) v = IterativeDomain.leaf v := by
      cases h
      rfl

    @[match_pattern]
    def IterativeDomain.abort {n} : (IterativeDomain «Σ» Γ α β n).carrier := match n with
      | 0 => .inr .unit
      | _ + 1 => .inr (.inl .unit)

    @[push_cast]
    theorem IterativeDomain.abort_cast {m n} {h : m = n} :
        h ▸ IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := m) (β := β) = IterativeDomain.abort := by
      cases h
      rfl

    @[simp]
    theorem IterativeDomain.idist_abort_abort {n} :
        idist (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n)) IterativeDomain.abort = ⊥ := by
      cases n <;> rfl

    @[simp]
    theorem IterativeDomain.idist_abort_leaf {n} {v : β} :
        idist (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := n)) (IterativeDomain.leaf v) = ⊤ := by
      cases n <;> rfl

    @[simp]
    theorem IterativeDomain.idist_leaf_abort {n} {v : β} :
        idist (IterativeDomain.leaf v) (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (n := n)) = ⊤ := by
      cases n <;> rfl

    @[match_pattern]
    def IterativeDomain.branch {n} (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)) :
        (IterativeDomain «Σ» Γ α β (n + 1)).carrier :=
      .inr <| .inr f

    lemma jsp {m n} (h : m + 1 = n) : n - 1 + 1 = n := by grind only

    @[push_cast]
    theorem IterativeDomain.branch_cast {m n} (h : m + 1 = n + 1) (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β m).carrier)) :
        h ▸ IterativeDomain.branch f = IterativeDomain.branch λ σ ↦ (propext Nat.add_one_inj).mp h ▸ f σ := by
      cases h
      rfl

    theorem IterativeDomain.branch_cast' {m n} (h : m + 1 = n) (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β m).carrier)) :
        h ▸ IterativeDomain.branch f = jsp h ▸ IterativeDomain.branch λ σ ↦ Nat.eq_sub_of_add_eq h ▸ f σ := by
      cases h
      rfl

    @[simp]
    theorem IterativeDomain.idist_leaf_branch {n} {v : β} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.leaf v) (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    theorem IterativeDomain.idist_branch_leaf {n} {v : β} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) (IterativeDomain.leaf v) = ⊤ := by
      rfl

    @[simp]
    theorem IterativeDomain.idist_abort_branch {n} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist IterativeDomain.abort (IterativeDomain.branch f) = ⊤ := by
      rfl

    @[simp]
    theorem IterativeDomain.idist_branch_abort {n} {f : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) IterativeDomain.abort = ⊤ := by
      rfl

    @[simp]
    theorem IterativeDomain.idist_branch_branch {n} {f g : «Σ» →ᵤ Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier)} :
        idist (IterativeDomain.branch f) (IterativeDomain.branch g) = ⨆ σ, IMetric.hausdorffIDist (f σ) (g σ) := by
      erw [UniformFun.idist_eq_iSup]

    @[push_cast]
    theorem IterativeDomain.Branch.cast_recv {m n} (h : m = n) {π : α →ᵤ Bool →ᵤ Restriction (IterativeDomain «Σ» Γ α β m).carrier unitInterval.half} {c : Γ} :
        h ▸ Branch.recv («Σ» := «Σ») c π = Branch.recv c λ v ok ↦ { val := h ▸ (π v ok).val } := by
      cases h
      rfl

    @[push_cast]
    theorem IterativeDomain.Branch.cast_send {m n} (h : m = n) {c : Γ} {v : α} {p : Restriction (IterativeDomain «Σ» Γ α β m).carrier unitInterval.half} :
        h ▸ Branch.send («Σ» := «Σ») c v p = Branch.send c v { val := h ▸ p.val } := by
      cases h
      rfl

    @[push_cast]
    theorem IterativeDomain.Branch.cast_close {m n} (h : m = n) {c : Γ} {p : Restriction (IterativeDomain «Σ» Γ α β m).carrier unitInterval.half} :
        h ▸ Branch.close («Σ» := «Σ») (α := α) c p = Branch.close c { val := h ▸ p.val } := by
      cases h
      rfl

    @[push_cast]
    theorem IterativeDomain.Branch.cast_sync {m n} (h : m = n) {c : Γ} {p : Restriction (IterativeDomain «Σ» Γ α β m).carrier unitInterval.half} :
        h ▸ Branch.sync («Σ» := «Σ») (α := α) c p = Branch.sync c { val := h ▸ p.val } := by
      cases h
      rfl

    @[push_cast]
    theorem IterativeDomain.Branch.cast_next {m n} (h : m = n) {σ : «Σ»} {p : Restriction (IterativeDomain «Σ» Γ α β m).carrier unitInterval.half} :
        h ▸ Branch.next (Γ := Γ) (α := α) σ p = Branch.next σ { val := h ▸ p.val } := by
      cases h
      rfl

    section Lift
      /-! ## Lifting depth of trees -/

      def Branch.map {γ'} (g : γ → γ') :
          (Branch «Σ» Γ α γ) → (Branch «Σ» Γ α γ') :=
        Sum.map (Prod.map id (UniformFun.map (UniformFun.map (Restriction.map g)))) <|
        Sum.map (Prod.map id (Prod.map id (Restriction.map g))) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
        Sum.map (Prod.map id (Restriction.map g)) <|
                (Prod.map id (Restriction.map g))

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_recv {γ'} {f : γ → γ'} {c : Γ} {π : α →ᵤ Bool →ᵤ Restriction γ unitInterval.half} :
          Branch.map f (Branch.recv («Σ» := «Σ») c π) = Branch.recv c λ v ok ↦ Restriction.map f (π v ok) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_send {γ'} {f : γ → γ'} {c : Γ} {v : α} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.send («Σ» := «Σ») c v x) = Branch.send c v (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_close {γ'} {f : γ → γ'} {c : Γ} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.close («Σ» := «Σ») (α := α) c x) = Branch.close c (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_sync {γ'} {f : γ → γ'} {c : Γ} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.sync («Σ» := «Σ») (α := α) c x) = Branch.sync c (Restriction.map f x) := by
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] [PseudoIMetricSpace Γ] in
      theorem Branch.map_next {γ'} {f : γ → γ'} {σ : «Σ»} {x : Restriction γ unitInterval.half} :
          Branch.map f (Branch.next (Γ := Γ) (α := α) σ x) = Branch.next σ (Restriction.map f x) := by
        rfl

      @[push_cast]
      theorem IterativeDomain.Branch.map_cast_right {m n o} (h : n = o) {b : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β m).carrier}
        {f : (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α γ n).carrier} :
          h ▸ Branch.map f b = Branch.map (λ x ↦ h ▸ f x) b := by
        cases h
        rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_eq_recv {γ'} {c : Γ} {π : α →ᵤ Bool →ᵤ Restriction γ' unitInterval.half} {f : γ → γ'}
        {b : Branch «Σ» Γ α γ} (h : Branch.map f b = Branch.recv c π) :
          ∃ π', b = Branch.recv c π' := by
        cases b with
        | recv c π' =>
          rw [Branch.map_recv] at h
          injections _ c_eq π_eq
          subst c
          exists π'
        | send c v p' =>
          rw [Branch.map_send] at h
          injections
        | close c p' =>
          rw [Branch.map_close] at h
          injections
        | sync c p' =>
          rw [Branch.map_sync] at h
          injections
        | next σ p' =>
          rw [Branch.map_next] at h
          injections

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_eq_recv' {γ'} {c : Γ} {π : α →ᵤ Bool →ᵤ Restriction γ' unitInterval.half} {f : γ → γ'}
        {b : Branch «Σ» Γ α γ} (h : Branch.map f b = Branch.recv c π) :
          ∃ π', b = Branch.recv c π' ∧ π = (λ v ok ↦ Restriction.map f (π' v ok)) := by
        cases b with
        | recv c π' =>
          rw [Branch.map_recv] at h
          injections _ c_eq π_eq
          subst c π
          exists π'
        | send c v p =>
          rw [Branch.map_send] at h
          injections
        | close c p =>
          rw [Branch.map_close] at h
          injections
        | sync c p =>
          rw [Branch.map_sync] at h
          injections
        | next σ p =>
          rw [Branch.map_next] at h
          injections

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_eq_send {γ'} {c : Γ} {v : α} {p : Restriction γ' unitInterval.half} {f : γ → γ'}
        {b : Branch «Σ» Γ α γ} (h : Branch.map f b = Branch.send c v p) :
          ∃ p', b = Branch.send c v p' := by
        cases b with
        | recv c π' =>
          rw [Branch.map_recv] at h
          injections
        | send c v p' =>
          rw [Branch.map_send] at h
          injections _ _ c_eq _ v_eq
          subst c v
          exists p'
        | close c p' =>
          rw [Branch.map_close] at h
          injections
        | sync c p' =>
          rw [Branch.map_sync] at h
          injections
        | next σ p' =>
          rw [Branch.map_next] at h
          injections

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_eq_send' {γ'} {c : Γ} {v : α} {p : Restriction γ' unitInterval.half} {f : γ → γ'}
        {b : Branch «Σ» Γ α γ} (h : Branch.map f b = Branch.send c v p) :
          ∃ p', b = Branch.send c v p' ∧ p = Restriction.map f p' := by
        cases b with
        | recv c π =>
          rw [Branch.map_recv] at h
          injections
        | send c v p =>
          rw [Branch.map_send] at h
          injections _ _ c_eq _ v_eq p_eq
          subst c v
          use p, rfl, p_eq.symm
        | close c p =>
          rw [Branch.map_close] at h
          injections
        | sync c p =>
          rw [Branch.map_sync] at h
          injections
        | next σ p =>
          rw [Branch.map_next] at h
          injections

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_eq_close {γ'} {c : Γ} {p : Restriction γ' unitInterval.half} {f : γ → γ'}
        {b : Branch «Σ» Γ α γ} (h : Branch.map f b = Branch.close c p) :
          ∃ p', b = Branch.close c p' := by
        cases b with
        | recv c π' =>
          rw [Branch.map_recv] at h
          injections
        | send c v p' =>
          rw [Branch.map_send] at h
          injections
        | close c p' =>
          rw [Branch.map_close] at h
          injections _ _ _ c_eq
          subst c
          exists p'
        | sync c p' =>
          rw [Branch.map_sync] at h
          injections
        | next σ p' =>
          rw [Branch.map_next] at h
          injections

      theorem Branch.map_isometry' {γ' : Type y} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : ∀ x y : γ, idist (g x) (g y) = idist x y) :
          ∀ (x y : Branch «Σ» Γ α γ), idist (Branch.map g x) (Branch.map g y) = idist x y := by
        rintro (_|_|_|_|_) (_|_|_|_|_) <;> first | rfl | dsimp [map]
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply UniformFun.map_isometry'
            intros _ _
            apply UniformFun.map_isometry'
            intros _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Isometry.prodMap'
            · exact λ _ _ ↦ rfl
            · intros _ _
              apply Restriction.map_isometry'
              exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg
        · apply Isometry.prodMap'
          · exact λ _ _ ↦ rfl
          · intros _ _
            apply Restriction.map_isometry'
            exact hg

      theorem Branch.map_isometry {γ' : Type y} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : Isometry g) :
          Isometry (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Isometry.of_idist_eq
        apply Branch.map_isometry'
        apply Isometry.to_idist_eq
        assumption

      theorem Branch.map_uniform_continuous {γ'} [PseudoIMetricSpace γ'] {g : γ → γ'} (hg : UniformContinuous g) :
          UniformContinuous (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) := by
        apply Topology.UniformContinuous.sumMap
        · apply UniformContinuous.prodMap
          · exact uniformContinuous_id
          · apply UniformFun.uniformContinuous_map
            apply UniformFun.uniformContinuous_map
            apply Restriction.uniformContinuous_map
            exact hg
        · apply Topology.UniformContinuous.sumMap
          · apply UniformContinuous.prodMap
            · exact uniformContinuous_id
            · apply UniformContinuous.prodMap
              · exact uniformContinuous_id
              · apply Restriction.uniformContinuous_map
                exact hg
          · apply Topology.UniformContinuous.sumMap
            · apply UniformContinuous.prodMap
              · exact uniformContinuous_id
              · apply Restriction.uniformContinuous_map
                exact hg
            · apply Topology.UniformContinuous.sumMap
              · apply UniformContinuous.prodMap
                · exact uniformContinuous_id
                · apply Restriction.uniformContinuous_map
                  exact hg
              · apply UniformContinuous.prodMap
                · exact uniformContinuous_id
                · apply Restriction.uniformContinuous_map
                  exact hg

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_comp {γ' γ''} [PseudoIMetricSpace γ'] [PseudoIMetricSpace γ''] (f : γ → γ') (g : γ' → γ'') :
          (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) g) ∘ (Branch.map f) = (Branch.map (g ∘ f)) := by
        funext b
        cases b <;> rfl

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_comp' {γ' γ''} [PseudoIMetricSpace γ'] [PseudoIMetricSpace γ''] (f : γ → γ') (g : γ' → γ'') {b : Branch «Σ» Γ α γ} :
          Branch.map g (Branch.map f b) = Branch.map (g ∘ f) b := by
        change (Branch.map g ∘ Branch.map f) b = _
        rw [Branch.map_comp]

      omit [PseudoIMetricSpace «Σ»] [PseudoIMetricSpace Γ] [PseudoIMetricSpace α] [PseudoIMetricSpace γ] in
      theorem Branch.map_id : (Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (γ := γ) id) = id := by
        funext b
        apply b.casesOn <;> solve_by_elim

      lemma Branch.map_idist_le_left'
        {γ γ' : Type _} [PseudoIMetricSpace γ] [PseudoIMetricSpace γ']
        {g g' : γ → γ'} {r : ℝ} (hr' : 0 ≤ r)
        (hr : ∀ x : γ, unitInterval.half * idist (g x) (g' x) ≤ r)
        (b : Branch «Σ» Γ α γ) :
          idist (Branch.map g b) (Branch.map g' b) ≤ r := by
        cases b with
        | recv c f =>
          dsimp [Branch.recv, Branch.map]
          rw [← UniformFun.idist_eq]
          rw [UniformFun.idist_eq_iSup₂]
          -- change max (idist c c) (⨆ v, ⨆ ok, unitInterval.half * idist (g (f v ok).val) (g' (f v ok).val)) ≤ _
          rw [idist_self, ← unitInterval.bot_eq, max_eq_right]
          · apply unitInterval.coe_iSup₂_le hr'
            intros v ok
            simp only [UniformFun.map_apply]
            apply Restriction.map_idist_le'
            apply hr
          · rw [Subtype.coe_le_coe]
            apply OrderBot.bot_le
        | send c v p =>
          change max (idist c c) (max (idist v v) (unitInterval.half * idist (g p.val) (g' p.val))) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | close c p =>
          change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | sync c p =>
          change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr
        | next σ p =>
          change max (idist σ σ) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

          repeat erw [idist_self, bot_sup_eq]
          apply hr

      lemma Branch.map_idist_le_left
        {γ γ' : Type _} [PseudoIMetricSpace γ] [PseudoIMetricSpace γ']
        {g g' : γ → γ'} {r : unitInterval}
        (hr : ∀ x : γ, unitInterval.half * idist (g x) (g' x) ≤ r)
        (b : Branch «Σ» Γ α γ) :
          idist (Branch.map g b) (Branch.map g' b) ≤ r := by
        apply Branch.map_idist_le_left'
        · exact unitInterval.nonneg r
        · assumption

      lemma Branch.map_idist_le_right'
        {γ γ' : Type _} [PseudoIMetricSpace γ] [PseudoIMetricSpace γ']
        {g : γ → γ'} {r : ℝ} (hr' : 1 ≤ r)
        (hr : ∀ x y : γ, idist (g x) (g y) ≤ r * idist x y)
        (b b' : Branch «Σ» Γ α γ) :
          idist (Branch.map g b) (Branch.map g b') ≤ r * idist b b' := by
        cases b <;> cases b'

        case recv.recv c π c' π' =>
          erw [Branch.map_recv, Branch.map_recv, Branch.idist_recv_recv, Branch.idist_recv_recv,
               mul_max_of_nonneg]
          · apply max_le_max
            · apply le_mul_of_one_le_left
              · apply unitInterval.nonneg
              · exact hr'
            · rw [UniformFun.idist_eq_iSup₂]
              apply unitInterval.coe_iSup₂_le ?_ λ b b' ↦ ?_
              · apply mul_nonneg
                · exact le_trans zero_le_one hr'
                · apply unitInterval.nonneg
              · apply Restriction.map_idist_le'

                rw [UniformFun.idist_eq_iSup₂]
                simp_rw [← unitInterval.mul_iSup]
                rw [Set.Icc.coe_mul, ← mul_assoc, mul_comm (a := r), mul_assoc]
                apply mul_le_mul (le_refl _)
                · apply le_trans
                  · apply hr
                  · apply mul_le_mul (le_refl _)
                    · apply unitInterval.coe_le_iSup₂ (f := λ x y ↦ idist (π x y).val (π' x y).val)
                    · apply unitInterval.nonneg
                    · exact le_trans zero_le_one hr'
                · apply unitInterval.nonneg
                · apply unitInterval.nonneg
          · exact le_trans zero_le_one hr'
        case send.send =>
          erw [Branch.map_send, Branch.map_send, Branch.idist_send_send, Branch.idist_send_send,
               mul_max_of_nonneg, mul_max_of_nonneg]
          · apply max_le_max
            · apply max_le_max
              · apply le_mul_of_one_le_left
                · unit_interval
                · exact hr'
              · apply le_mul_of_one_le_left
                · unit_interval
                · exact hr'
            · simp_rw [Restriction.idist_eq]
              rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← mul_assoc, mul_comm (a := r), mul_assoc]
              apply mul_le_mul (le_refl _)
              · apply hr
              · apply unitInterval.nonneg
              · apply unitInterval.nonneg
          · exact le_trans zero_le_one hr'
          · exact le_trans zero_le_one hr'
        case close.close =>
          erw [Branch.map_close, Branch.map_close, Branch.idist_close_close, Branch.idist_close_close,
               mul_max_of_nonneg]
          · apply max_le_max
            · apply le_mul_of_one_le_left
              · unit_interval
              · exact hr'
            · simp_rw [Restriction.idist_eq]
              rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← mul_assoc, mul_comm (a := r), mul_assoc]
              apply mul_le_mul (le_refl _)
              · apply hr
              · apply unitInterval.nonneg
              · apply unitInterval.nonneg
          · exact le_trans zero_le_one hr'
        case sync.sync =>
          erw [Branch.map_sync, Branch.map_sync, Branch.idist_sync_sync, Branch.idist_sync_sync,
               mul_max_of_nonneg]
          · apply max_le_max
            · apply le_mul_of_one_le_left
              · unit_interval
              · exact hr'
            · simp_rw [Restriction.idist_eq]
              rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← mul_assoc, mul_comm (a := r), mul_assoc]
              apply mul_le_mul (le_refl _)
              · apply hr
              · apply unitInterval.nonneg
              · apply unitInterval.nonneg
          · exact le_trans zero_le_one hr'
        case next.next =>
          erw [Branch.map_next, Branch.map_next, Branch.idist_next_next, Branch.idist_next_next,
               mul_max_of_nonneg]
          · apply max_le_max
            · apply le_mul_of_one_le_left
              · unit_interval
              · exact hr'
            · simp_rw [Restriction.idist_eq]
              rw [Set.Icc.coe_mul, Set.Icc.coe_mul, ← mul_assoc, mul_comm (a := r), mul_assoc]
              apply mul_le_mul (le_refl _)
              · apply hr
              · apply unitInterval.nonneg
              · apply unitInterval.nonneg
          · exact le_trans zero_le_one hr'

        all:
          change 1 ≤ r * 1
          rwa [mul_one]

        -- cases b with
        -- | recv c f =>
        --   dsimp [Branch.recv, Branch.map]
        --   -- change max (idist c c) (idist (UniformFun.map (UniformFun.map (Restriction.map g)) f) (UniformFun.map (UniformFun.map (Restriction.map g')) f)) ≤ _
        --   simp_rw [UniformFun.idist_eq_iSup]
        --   -- change max (idist c c) (⨆ v, ⨆ ok, unitInterval.half * idist (g (f v ok).val) (g' (f v ok).val)) ≤ _
        --   rw [idist_self, ← unitInterval.bot_eq, max_eq_right]
        --   · apply unitInterval.coe_iSup₂_le hr'
        --     intros v ok
        --     apply hr
        --   · rw [Subtype.coe_le_coe]
        --     apply OrderBot.bot_le
        -- | send c v p =>
        --   change max (idist c c) (max (idist v v) (unitInterval.half * idist (g p.val) (g' p.val))) ≤ r

        --   repeat erw [idist_self, bot_sup_eq]
        --   apply hr
        -- | close c p =>
        --   change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

        --   repeat erw [idist_self, bot_sup_eq]
        --   apply hr
        -- | sync c p =>
        --   change max (idist c c) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

        --   repeat erw [idist_self, bot_sup_eq]
        --   apply hr
        -- | next σ p =>
        --   change max (idist σ σ) (unitInterval.half * idist (g p.val) (g' p.val)) ≤ r

        --   repeat erw [idist_self, bot_sup_eq]
        --   apply hr

      def IterativeDomain.lift {m n} (h : m ≤ n := by linarith) :
          (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier := match _hm : m, n with
        | 0, 0 => id
        | 0, n + 1 => Sum.elim (λ v ↦ .inl v) (λ .unit ↦ IterativeDomain.abort)
        | m + 1, n + 1 =>
          Sum.map id <|
            Sum.map id <|
              UniformFun.map <| Set.image (Branch.map (IterativeDomain.lift (m := m)))

      @[simp]
      theorem IterativeDomain.lift_leaf {m n} (h : m ≤ n) {v : β} :
          (IterativeDomain.lift h (IterativeDomain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) v)) = IterativeDomain.leaf v := by
        cases m <;> fun_induction IterativeDomain <;> first
          | rfl
          | grind

      @[simp]
      theorem IterativeDomain.lift_abort {m n} (h : m ≤ n) :
          (IterativeDomain.lift h (IterativeDomain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β))) = IterativeDomain.abort := by
        cases m <;> fun_induction IterativeDomain <;> first
          | rfl
          | grind

      @[simp]
      theorem IterativeDomain.lift_branch {m n} (h : m + 1 ≤ n + 1) {f : «Σ» →ᵤ Set (Branch «Σ» Γ α _)} :
          IterativeDomain.lift h (IterativeDomain.branch (β := β) f) = IterativeDomain.branch λ σ ↦ Branch.map (IterativeDomain.lift (m := m)) '' f σ := by
        rfl

      theorem IterativeDomain.lift_branch' {m n} (h : m + 1 ≤ n) {f : «Σ» →ᵤ Set (Branch «Σ» Γ α _)} :
          IterativeDomain.lift h (IterativeDomain.branch (β := β) f) =
            Nat.sub_one_add_one (Nat.ne_zero_of_lt h) ▸
              IterativeDomain.branch λ σ ↦ Branch.map (IterativeDomain.lift (Nat.le_pred_of_succ_le h)) '' f σ := by
        obtain ⟨n', rfl⟩ := Nat.succ_le_exists_succ h
        rw [IterativeDomain.lift_branch h]
        rfl

      @[push_cast]
      theorem IterativeDomain.lift_cast_left_right {m n o} {h : m ≤ n} {h' : n = o} {p : (IterativeDomain «Σ» Γ α β m).carrier} :
          h' ▸ IterativeDomain.lift h p = IterativeDomain.lift (h' ▸ h) p := by
        cases h'
        rfl

      theorem IterativeDomain.lift_cast_right {m n o} {h : m ≤ n} {h' : m = o} {p : (IterativeDomain «Σ» Γ α β m).carrier} :
          IterativeDomain.lift (h' ▸ h) (h' ▸ p) = IterativeDomain.lift h p := by
        cases h'
        rfl

      theorem IterativeDomain.lift_refl {m} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := m) (Nat.le_of_eq rfl) = id := by
        cases m with
        | zero => rfl
        | succ m =>
          ext x : 2
          match x with
          | .inl _ | .inr (.inl _) => rfl
          | .inr (.inr f) =>
            dsimp [lift]
            congr 2
            funext b
            rw [UniformFun.map_apply]
            convert Set.image_id _
            convert Branch.map_id
            rw [lift_refl]

      theorem IterativeDomain.lift_refl_of_eq {k k' m n} (h : m = n) (h' : k = k') {h'' : m ≤ k} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h'' = h ▸ h' ▸ lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (m := n) (n := k') (h ▸ h' ▸ h'') := by
        cases h
        cases h'
        rfl

      theorem IterativeDomain.lift_refl_of_eq' {k k' m n} (h : m = n) (h' : k = k') {h'' : m ≤ k} {x} :
          lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h'' x = h' ▸ lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (m := n) (n := k') (h ▸ h' ▸ h'') (h ▸ x) := by
        cases h
        cases h'
        rfl

      theorem IterativeDomain.lift_isometry {m n} (h : m ≤ n) :
          Isometry (lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h) := by
        match m, n with
        | 0, 0 => exact isometry_id
        | 0, n + 1 => rintro (_|_) (_|_) <;> rfl
        | m + 1, n + 1 =>
          apply Isometry.sumMap
          · exact isometry_id
          · apply Isometry.sumMap
            · exact isometry_id
            · apply UniformFun.map_isometry
              apply Set.image_isometry
              apply Branch.map_isometry
              apply lift_isometry

      theorem IterativeDomain.lift_isometry' {m n} (h : m ≤ n) {x y : (IterativeDomain «Σ» Γ α β m).carrier} :
          idist (lift h x) (lift h y) = idist x y := by
        apply Isometry.to_idist_eq
        exact lift_isometry h

      theorem IterativeDomain.lift_lift {m n o} (h₁ : m ≤ n) (h₂ : n ≤ o) :
          (lift («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) h₂) ∘ (lift h₁) = (lift (le_trans h₁ h₂)) := by
        funext x
        match m, n, o with
        | 0, 0, 0 | 0, 0, o + 1 => rfl
        | 0, n + 1, o + 1 => cases x <;> rfl
        | m + 1, n + 1, o + 1 =>
          match x with
          | .inl b | .inr (.inl _) => rfl
          | .inr (.inr f) =>
            dsimp [lift]
            congr 2; funext σ
            rw [UniformFun.map_apply, UniformFun.map_apply, UniformFun.map_apply, Set.image_image]
            change (Branch.map _ ∘ Branch.map _) '' (f σ) = _
            rw! [Branch.map_comp, lift_lift]
            rfl

      theorem IterativeDomain.lift_lift' {m n o} (h₁ : m ≤ n) (h₂ : n ≤ o) {p : (IterativeDomain «Σ» Γ α β m).carrier} :
          lift h₂ (lift h₁ p) = lift (le_trans h₁ h₂) p := by
        change (lift h₂ ∘ lift h₁) p = _
        rw [lift_lift]

      theorem IterativeDomain.idist_lift_lift {m n o o'} (h₁ : m ≤ o) (h₂ : n ≤ o) (h₃ : m ≤ o') (h₄ : n ≤ o')
        {p : (IterativeDomain «Σ» Γ α β m).carrier} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
          idist (IterativeDomain.lift h₁ p) (IterativeDomain.lift h₂ q) = idist (IterativeDomain.lift h₃ p) (IterativeDomain.lift h₄ q) := by
        match m, n, p, q with
        | 0, 0, IterativeDomain.leaf v, IterativeDomain.leaf v'
        | 0, n + 1, IterativeDomain.leaf v, IterativeDomain.leaf v'
        | m + 1, 0, IterativeDomain.leaf v, IterativeDomain.leaf v'
        | m + 1, n + 1, IterativeDomain.leaf v, IterativeDomain.leaf v' =>
          repeat rw [IterativeDomain.lift_leaf]
          repeat rw [IterativeDomain.idist_leaf_leaf]
        | 0, 0, IterativeDomain.abort, IterativeDomain.abort
        | 0, n + 1, IterativeDomain.abort, IterativeDomain.abort
        | m + 1, 0, IterativeDomain.abort, IterativeDomain.abort
        | m + 1, n + 1, IterativeDomain.abort, IterativeDomain.abort =>
          repeat rw [IterativeDomain.lift_abort]
          repeat rw [IterativeDomain.idist_abort_abort]
        | 0, 0, IterativeDomain.leaf v, IterativeDomain.abort
        | 0, n + 1, IterativeDomain.leaf v, IterativeDomain.abort
        | m + 1, 0, IterativeDomain.leaf v, IterativeDomain.abort
        | m + 1, n + 1, IterativeDomain.leaf v, IterativeDomain.abort
        | 0, 0, IterativeDomain.abort, IterativeDomain.leaf v'
        | 0, n + 1, IterativeDomain.abort, IterativeDomain.leaf v'
        | m + 1, 0, IterativeDomain.abort, IterativeDomain.leaf v'
        | m + 1, n + 1, IterativeDomain.abort, IterativeDomain.leaf v' =>
          repeat rw [IterativeDomain.lift_leaf, IterativeDomain.lift_abort]
          repeat
            first | rw [IterativeDomain.idist_leaf_abort]
                  | rw [IterativeDomain.idist_abort_leaf]
        | 0, n + 1, IterativeDomain.leaf v, IterativeDomain.branch f'
        | m + 1, n + 1, IterativeDomain.leaf v, IterativeDomain.branch f' =>
          repeat rw [IterativeDomain.lift_leaf, IterativeDomain.lift_branch']
          rw [← IterativeDomain.leaf_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₂)),
              ← IterativeDomain.leaf_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₄)),
              ← IterativeDomain.idist_cast, ← IterativeDomain.idist_cast,
              IterativeDomain.idist_leaf_branch, IterativeDomain.idist_leaf_branch]
        | m + 1, 0, IterativeDomain.branch f, IterativeDomain.leaf v'
        | m + 1, n + 1, IterativeDomain.branch f, IterativeDomain.leaf v' =>
          repeat rw [IterativeDomain.lift_leaf, IterativeDomain.lift_branch']
          rw [← IterativeDomain.leaf_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₁)),
              ← IterativeDomain.leaf_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₃)),
              ← IterativeDomain.idist_cast, ← IterativeDomain.idist_cast,
              IterativeDomain.idist_branch_leaf, IterativeDomain.idist_branch_leaf]
        | 0, n + 1, IterativeDomain.abort, IterativeDomain.branch f'
        | m + 1, n + 1, IterativeDomain.abort, IterativeDomain.branch f' =>
          repeat rw [IterativeDomain.lift_abort, IterativeDomain.lift_branch']
          rw [← IterativeDomain.abort_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₂)),
              ← IterativeDomain.abort_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₄)),
              ← IterativeDomain.idist_cast, ← IterativeDomain.idist_cast,
              IterativeDomain.idist_abort_branch, IterativeDomain.idist_abort_branch]
        | m + 1, 0, IterativeDomain.branch f, IterativeDomain.abort
        | m + 1, n + 1, IterativeDomain.branch f, IterativeDomain.abort =>
          repeat rw [IterativeDomain.lift_abort, IterativeDomain.lift_branch']
          rw [← IterativeDomain.abort_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₁)),
              ← IterativeDomain.abort_cast (h := Nat.sub_one_add_one (Nat.ne_zero_of_lt h₃)),
              ← IterativeDomain.idist_cast, ← IterativeDomain.idist_cast,
              IterativeDomain.idist_branch_abort, IterativeDomain.idist_branch_abort]
        | m + 1, n + 1, IterativeDomain.branch f, IterativeDomain.branch f' =>
          repeat rw [IterativeDomain.lift_branch']
          repeat rw [← IterativeDomain.idist_cast, IterativeDomain.idist_branch_branch]
          apply iSup_congr λ σ ↦ ?_
          apply IMetric.hausdorffIDist_congr₂' λ b b' ↦ ?_

          cases b <;> cases b'

          case recv.recv =>
            erw [Branch.idist_recv_recv, Branch.idist_recv_recv]
            simp_rw [UniformFun.idist_eq_iSup₂, UniformFun.map_apply, Restriction.map,
                     Restriction.idist_eq]
            dsimp
            congr 1
            apply iSup_congr λ v ↦ ?_
            apply iSup_congr λ ok ↦ ?_
            congr 1
            apply IterativeDomain.idist_lift_lift
          case send.send =>
            erw [Branch.idist_send_send, Branch.idist_send_send,
                 Restriction.map, Restriction.map, Restriction.idist_eq, Restriction.idist_eq]
            dsimp
            congr 2
            apply IterativeDomain.idist_lift_lift
          case close.close =>
            erw [Branch.idist_close_close, Branch.idist_close_close,
                 Restriction.map, Restriction.map, Restriction.idist_eq, Restriction.idist_eq]
            dsimp
            congr 2
            apply IterativeDomain.idist_lift_lift
          case sync.sync =>
            erw [Branch.idist_sync_sync, Branch.idist_sync_sync,
                 Restriction.map, Restriction.map, Restriction.idist_eq, Restriction.idist_eq]
            dsimp
            congr 2
            apply IterativeDomain.idist_lift_lift
          case next.next =>
            erw [Branch.idist_next_next, Branch.idist_next_next,
                 Restriction.map, Restriction.map, Restriction.idist_eq, Restriction.idist_eq]
            dsimp
            congr 2
            apply IterativeDomain.idist_lift_lift

          all:
            rfl
    end Lift

    section Truncation
      def IterativeDomain.trunc : ∀ {n m : ℕ}, n ≤ m → (IterativeDomain «Σ» Γ α β m).carrier → (IterativeDomain «Σ» Γ α β n).carrier
        | 0, 0,     _, x => x
        | 0, _ + 1, _, x => Sum.elim Sum.inl (λ _ ↦ .inr .unit) x
        | _ + 1, _ + 1, h, x =>
          Sum.elim Sum.inl
            (Sum.elim (Sum.inr ∘ Sum.inl) λ f ↦
              .inr <| .inr λ σ ↦
                Branch.map (IterativeDomain.trunc (Nat.le_of_succ_le_succ h)) '' f σ)
            x
    end Truncation
  end

  def DomainUnion := Σ n, (IterativeDomain «Σ» Γ α β n).carrier

  section
    variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

    abbrev DomainUnion.mk {n : ℕ} (x : (IterativeDomain «Σ» Γ α β n).carrier) : DomainUnion «Σ» Γ α β :=
      ⟨n, x⟩

    nonrec abbrev DomainUnion.idist : DomainUnion «Σ» Γ α β → DomainUnion «Σ» Γ α β → unitInterval
      | ⟨m, p⟩, ⟨n, q⟩ => idist (IterativeDomain.lift (le_max_left m n) p) (IterativeDomain.lift (le_max_right m n) q)

    theorem DomainUnion.idist_self (x : DomainUnion «Σ» Γ α β) : DomainUnion.idist x x = 0 := by
      let ⟨m, p⟩ := x
      grind only [PseudoIMetricSpace.idist_self, unitInterval.coe_ne_zero]

    theorem DomainUnion.idist_comm (x y : DomainUnion «Σ» Γ α β) : DomainUnion.idist x y = DomainUnion.idist y x := by
      let ⟨m, p⟩ := x; let ⟨n, q⟩ := y
      grind only [PseudoIMetricSpace.idist_comm]

    nonrec theorem DomainUnion.idist_triangle (x y z : DomainUnion «Σ» Γ α β) : (DomainUnion.idist x z : ℝ) ≤ (DomainUnion.idist x y) + (DomainUnion.idist y z) := by
      let ⟨m, p⟩ := x; let ⟨n, q⟩ := y; let ⟨o, r⟩ := z

      let k := max m (max n o)

      dsimp only [DomainUnion.idist]
      rw [← IterativeDomain.lift_isometry' (by grind only [= max_def] : max m o ≤ k),
          ← IterativeDomain.lift_isometry' (by grind only [= max_def] : max m n ≤ k),
          ← IterativeDomain.lift_isometry' (by grind only [= max_def] : max n o ≤ k)]
      change (IDist.idist ((_ ∘ _) p) ((_ ∘ _) r) : ℝ) ≤ IDist.idist ((_ ∘ _) p) ((_ ∘ _) q) + IDist.idist ((_ ∘ _) q) ((_ ∘ _) r)
      repeat rw [IterativeDomain.lift_lift]
      apply idist_triangle _ _ _

    instance : PseudoIMetricSpace (DomainUnion «Σ» Γ α β) where
      idist := DomainUnion.idist
      idist_self := DomainUnion.idist_self
      idist_comm := DomainUnion.idist_comm
      idist_triangle := DomainUnion.idist_triangle

    theorem DomainUnion.idist_eq {m n} {p : (IterativeDomain «Σ» Γ α β m).carrier} {q : (IterativeDomain «Σ» Γ α β n).carrier} :
        IDist.idist (DomainUnion.mk p) (DomainUnion.mk q) = IDist.idist (IterativeDomain.lift (le_max_left m n) p) (IterativeDomain.lift (le_max_right m n) q) := by
      rfl

    instance [IsUltrametricIDist «Σ»] [IsUltrametricIDist Γ] [IsUltrametricIDist α] [IsUltrametricIDist β] :
        IsUltrametricIDist (DomainUnion «Σ» Γ α β) where
      idist_triangle_max x y z := by
        let ⟨m, x⟩ := x; let ⟨n, y⟩ := y; let ⟨o, z⟩ := z
        iterate 3 rw [DomainUnion.idist_eq]

        have h₁ : max m o ≤ max m (max n o) := by grind only [= max_def]
        have h₂ : n ≤ max m (max n o) := by grind only [= max_def]

        conv_lhs => rw [← IterativeDomain.lift_isometry' h₁]
        rw [IterativeDomain.lift_lift', IterativeDomain.lift_lift']
        grw [idist_triangle_max _ (IterativeDomain.lift h₂ y) _]
        apply max_le_max
        · suffices h₃ : max m n ≤ max m (max n o) by
            conv_rhs => rw [← IterativeDomain.lift_isometry' h₃]
            rw [IterativeDomain.lift_lift', IterativeDomain.lift_lift']

          grind only [= max_def]
        · suffices h₃ : max n o ≤ max m (max n o) by
            conv_rhs => rw [← IterativeDomain.lift_isometry' h₃]
            rw [IterativeDomain.lift_lift', IterativeDomain.lift_lift']

          grind only [= max_def]

    theorem DomainUnion.mk_isometry {n} : Isometry (DomainUnion.mk («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) (n := n)) := by
      apply Isometry.of_idist_eq λ x y ↦ ?_

      change IDist.idist (IterativeDomain.lift (le_max_left n n) x) (IterativeDomain.lift (le_max_right n n) y) = _
      rw [IterativeDomain.lift_isometry']

    lemma DomainUnion.lift_idist_zero {n m : ℕ} (h : n ≤ m)
        (x : (IterativeDomain «Σ» Γ α β n).carrier) :
        DomainUnion.idist ⟨n, x⟩ ⟨m, IterativeDomain.lift h x⟩ = 0 := by
      change IDist.idist (IterativeDomain.lift _ x) ((IterativeDomain.lift _ ∘ IterativeDomain.lift _) x) = 0
      rw [IterativeDomain.lift_lift, Isometry.to_idist_eq (IterativeDomain.lift_isometry _), PseudoIMetricSpace.idist_self]

    lemma IterativeDomain.trunc_idist {n m} (h : n ≤ m) (x : (IterativeDomain «Σ» Γ α β m).carrier) :
        (DomainUnion.idist ⟨m, x⟩ ⟨n, IterativeDomain.trunc h x⟩ : ℝ) ≤ (1/2 : ℝ) ^ n := by
      match n, m, h, x with
      | 0, _, _, _ => exact unitInterval.le_one _
      | n + 1, m + 1, h, IterativeDomain.leaf v =>
          change idist (IterativeDomain.lift _ _) _ ≤ unitInterval.half ^ (n + 1)
          erw [IterativeDomain.lift_leaf, IterativeDomain.lift_leaf, idist_self]
          bound
      | n + 1, m + 1, h, IterativeDomain.abort =>
          change idist (IterativeDomain.lift _ _) _ ≤ unitInterval.half ^ (n + 1)
          erw [IterativeDomain.lift_abort, IterativeDomain.lift_abort, idist_self]
          bound
      | n + 1, m + 1, h, IterativeDomain.branch f =>
          have max_eq : max (m + 1) (n + 1) = m + 1 := by grind only [= max_def]

          change idist (IterativeDomain.lift _ _) (IterativeDomain.lift _ (IterativeDomain.branch _)) ≤ unitInterval.half ^ (n + 1)

          repeat rw [IterativeDomain.lift_refl_of_eq' rfl max_eq]
          rw [← IterativeDomain.idist_cast, IterativeDomain.lift_refl]

          change idist (IterativeDomain.branch _) (IterativeDomain.lift _ (IterativeDomain.branch _)) ≤ unitInterval.half ^ (n + 1)

          repeat rw [IterativeDomain.lift_branch]
          rw [IterativeDomain.idist_branch_branch]

          apply iSup_le
          intro σ

          rw [← Set.image_comp, Branch.map_comp]
          trans
          · exact IMetric.hausdorffIDist_image_le_of_le_sup
          · apply iSup₂_le
            intros b b_in
            convert_to idist (Branch.map id b) _ ≤ _
            · rfl
            · rw [Branch.map_id]; rfl
            · apply Branch.map_idist_le_left
              intros x

              trans (unitInterval.half * unitInterval.half^n)
              · have IH := trunc_idist (Nat.add_one_le_add_one_iff.mp h) x

                have max_eq' : max m n = m := by grind only [= max_def]

                change idist (IterativeDomain.lift _ _) (IterativeDomain.lift _ _) ≤ unitInterval.half ^ n at IH

                repeat rw [IterativeDomain.lift_refl_of_eq' rfl max_eq'] at IH
                rw [← IterativeDomain.idist_cast, IterativeDomain.lift_refl] at IH

                change _ * idist x ((IterativeDomain.lift _ ∘ IterativeDomain.trunc _) x) ≤ _
                change idist x ((IterativeDomain.lift _ ∘ IterativeDomain.trunc _) x) ≤ _ at IH
                grw [IH]
              · rw [pow_add, pow_one, mul_comm]
  end

  abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β)

  example : MetricSpace (Domain «Σ» Γ α β) := inferInstance
  example : CompleteSpace (Domain «Σ» Γ α β) := inferInstance

  theorem _root_.UniformSpace.Completion.dist_le_iff {α} [PseudoMetricSpace α] {ε}
    (h : ∀ x y : α, dist x y ≤ ε) :
      ∀ x y : UniformSpace.Completion α, dist x y ≤ ε := by
    intros x y
    apply UniformSpace.Completion.induction_on₂ (p := (dist · · ≤ ε)) x y
    · exact isClosed_le continuous_dist continuous_const
    · simp_intro .. only [UniformSpace.Completion.dist_eq, h]

  instance {α} [PseudoIMetricSpace α] : IMetricSpace (UniformSpace.Completion α) :=
    .of_metric_space_of_dist_le_one <| UniformSpace.Completion.dist_le_iff λ x y ↦ unitInterval.le_one (idist x y)

  example : IMetricSpace (Domain «Σ» Γ α β) := inferInstance

  theorem UniformSpace.Completion.idist_eq {α : Type u} [PseudoIMetricSpace α] (x y : α) : idist (x : Completion α) y = idist x y := by
    change (⟨dist (x : Completion α) y, dist_nonneg, UniformSpace.Completion.dist_le_iff (λ x y ↦ unitInterval.le_one (idist x y)) _ _⟩ : unitInterval) = ⟨dist x y, dist_nonneg, unitInterval.le_one (idist x y)⟩
    congr 1
    rw [UniformSpace.Completion.dist_eq]

  instance {α} [PseudoIMetricSpace α] [IsUltrametricIDist α] : IsUltrametricIDist (UniformSpace.Completion α) where
    idist_triangle_max x y z := by
      induction x, y, z using UniformSpace.Completion.induction_on₃ with
      | hp =>
        apply isClosed_le
        · exact continuous_idist.comp (continuous_fst.prodMk continuous_snd.snd)
        · exact (continuous_idist.comp (continuous_fst.prodMk continuous_snd.fst)).sup
                   (continuous_idist.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      | ih x y z =>
        repeat rw [UniformSpace.Completion.idist_eq]
        apply idist_triangle_max

  variable [IsUltrametricIDist «Σ»] [IsUltrametricIDist Γ] [IsUltrametricIDist α] [IsUltrametricIDist β] in
  example : IsUltrametricIDist (Domain «Σ» Γ α β) := inferInstance

  theorem Domain.edist_eq {x y : Domain «Σ» Γ α β} : edist x y = ENNReal.ofReal (dist x y) := by
    rw [edist_dist]

  theorem Domain.dist_eq {x y : Domain «Σ» Γ α β} : dist x y = (idist x y : ℝ) := by
    rfl

  variable {«Σ» Γ α β γ δ} [PseudoIMetricSpace γ]

  section
    abbrev embedAt (n : ℕ) (x : (IterativeDomain «Σ» Γ α β n).carrier) : Domain «Σ» Γ α β :=
      ↑(DomainUnion.mk x)

    theorem embedAt_lift_eq {m n : ℕ} (h : m ≤ n) (p : (IterativeDomain «Σ» Γ α β m).carrier) :
        embedAt m p = embedAt n (IterativeDomain.lift h p) := by
      unfold embedAt
      apply eq_of_idist_eq_zero
      rw [UniformSpace.Completion.idist_eq]

      change idist (IterativeDomain.lift (le_max_left m n) p) ((IterativeDomain.lift (le_max_right m n) ∘ IterativeDomain.lift h) p) = 0

      rw [IterativeDomain.lift_lift, IterativeDomain.lift_isometry', idist_self]

    theorem embedAt_comp_lift_eq {m n : ℕ} (h : m ≤ n) :
        embedAt m = (embedAt n ∘ IterativeDomain.lift h : (IterativeDomain «Σ» Γ α β m).carrier → _) := by
      funext p
      exact embedAt_lift_eq h p

    theorem embedAt_isometry {m} :
        Isometry (embedAt («Σ» := «Σ») (Γ := Γ) (α := α) (β := β) m) := by
      unfold embedAt

      change Isometry (UniformSpace.Completion.coe' ∘ DomainUnion.mk)

      apply Isometry.comp
      · exact UniformSpace.Completion.coe_isometry
      · exact DomainUnion.mk_isometry

    lemma embedAt_idist_eq {n m : ℕ} (x : (IterativeDomain «Σ» Γ α β n).carrier)
        (y : (IterativeDomain «Σ» Γ α β m).carrier) :
        (idist (embedAt n x) (embedAt m y) : ℝ) = DomainUnion.idist ⟨n, x⟩ ⟨m, y⟩ := by
      erw [UniformSpace.Completion.idist_eq]

    def φ : DomainUnion «Σ» Γ α β → β ⊕ PUnit.{x + 1} ⊕ («Σ» →ᵤ Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β)))
      | ⟨0, IterativeDomain.leaf v⟩ | ⟨_ + 1, IterativeDomain.leaf v⟩ => .inl v
      | ⟨0, IterativeDomain.abort⟩ | ⟨_ + 1, IterativeDomain.abort⟩ => .inr (.inl .unit)
      | ⟨_ + 1, IterativeDomain.branch f⟩ =>
        .inr <| .inr λ σ ↦ {
          carrier := closure <| Branch.map (embedAt _) '' f σ
          isClosed' := isClosed_closure
        }

    lemma Domain.approx_uniform (d : Domain «Σ» Γ α β) (n : ℕ) :
        ∃ x : (IterativeDomain «Σ» Γ α β n).carrier,
          (idist d (embedAt n x) : ℝ) < 2 * (1/2 : ℝ) ^ n := by
      have hpos : (0 : ℝ) < (1/2 : ℝ) ^ n := pow_pos (by norm_num) _
      obtain ⟨⟨m, y⟩, hy⟩ :
          ∃ z : DomainUnion «Σ» Γ α β, (idist d (↑z : Domain «Σ» Γ α β) : ℝ) < (1/2 : ℝ) ^ n :=
        UniformSpace.Completion.denseRange_coe.exists_dist_lt d hpos
      rcases le_or_gt m n with hmn | hnm
      · exists IterativeDomain.lift hmn y
        have h0 : (idist (embedAt m y) (embedAt n (IterativeDomain.lift hmn y)) : ℝ) = 0 := by
          rw [embedAt_idist_eq, DomainUnion.lift_idist_zero hmn y]
          rfl
        linarith [idist_triangle (α := Domain «Σ» Γ α β) d (embedAt m y) (embedAt n (IterativeDomain.lift hmn y))]
      · exists IterativeDomain.trunc hnm.le y
        have htr : (idist (embedAt m y) (embedAt n (IterativeDomain.trunc hnm.le y)) : ℝ) ≤ (1/2)^n := by
          rw [embedAt_idist_eq]
          exact IterativeDomain.trunc_idist hnm.le y
        linarith [idist_triangle (α := Domain «Σ» Γ α β) d (embedAt m y) (embedAt n (IterativeDomain.trunc (LT.lt.le hnm) y))]

    lemma Branch.approx_uniform_depth (b : Branch «Σ» Γ α (Domain «Σ» Γ α β)) (n : ℕ) :
        ∃ b_n : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier,
          (idist b (Branch.map (embedAt n) b_n) : ℝ) ≤ (1/2) ^ n := by
      rcases b with ⟨γ₀, π⟩ | ⟨γ₀, a, d⟩ | ⟨γ₀, d⟩ | ⟨γ₀, d⟩ | ⟨s₀, d⟩
      · exists .recv γ₀ λ v ok => { val := Classical.choose (Domain.approx_uniform (π v ok).val n) }

        change max (idist γ₀ γ₀) (idist π _) ≤ unitInterval.half^n
        simp_rw [UniformFun.idist_eq_iSup]
        change max (idist γ₀ γ₀) (⨆ v, ⨆ ok, idist (π v ok) _) ≤ unitInterval.half^n
        rw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]
        apply iSup₂_le λ v ok ↦ ?_

        change unitInterval.half * idist (π v ok).val (embedAt n (Classical.choose (Domain.approx_uniform (π v ok).val n))) ≤ _

        have : (idist (π v ok).val (embedAt n (Classical.choose (Domain.approx_uniform (π v ok).val n))) : ℝ) < 2 * (1/2)^n :=
          Classical.choose_spec (Domain.approx_uniform (π v ok).val n)

        change ((1/2) * _ : ℝ) ≤ (1/2)^n
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .send γ₀ a { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (max (idist a a) (idist _ _)) : ℝ) ≤ _
        erw [idist_self, idist_self, ← unitInterval.bot_eq, bot_sup_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .close γ₀ { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .sync γ₀ { val := x_n }

        change ↑(@max unitInterval _ (idist γ₀ γ₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith
      · obtain ⟨x_n, hx⟩ := Domain.approx_uniform d.val n
        exists .next s₀ { val := x_n }

        change ↑(@max unitInterval _ (idist s₀ s₀) (idist _ _) : ℝ) ≤ _
        erw [idist_self, ← unitInterval.bot_eq, bot_sup_eq]

        change (1/2) * (idist d.val (embedAt n x_n) : ℝ) ≤ _
        linarith

    lemma Branch.approx_at_depth (b : Branch «Σ» Γ α (Domain «Σ» Γ α β)) {ε : ℝ} (hε : 0 < ε) :
        ∃ (n : _) (b_n : Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          idist b (Branch.map (embedAt n) b_n) < ε := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
      obtain ⟨b_n, hb⟩ := Branch.approx_uniform_depth b n
      exact ⟨n, b_n, hb.trans_lt hn⟩

    lemma Closeds.Branch.approx_uniform
        (h : «Σ» → TopologicalSpace.Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β)))
        {ε : ℝ} (hε : 0 < ε) :
        ∃ n : ℕ, ∀ σ, ∃ T : Set (Branch «Σ» Γ α (IterativeDomain «Σ» Γ α β n).carrier),
          IMetric.hausdorffIDist (closure (Branch.map (embedAt n) '' T)) (↑(h σ)) ≤ ε / 2 := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1/2 : ℝ) < 1)
      refine ⟨n, λ σ ↦ ⟨(λ b ↦ Classical.choose (Branch.approx_uniform_depth b n)) '' (h σ), ?_⟩⟩

      have hbound : ∀ b ∈ h σ,
          (idist b (Branch.map (embedAt n)
            (Classical.choose (Branch.approx_uniform_depth b n))) : ℝ) ≤ (1/2)^n :=
        λ b _ ↦ Classical.choose_spec (Branch.approx_uniform_depth b n)

      trans (1 / 2)^n
      · conv_lhs =>
          enter [1, 2];
          rw [← IsClosed.closure_eq (h := TopologicalSpace.Closeds.isClosed (h σ))]
        rw [IMetric.hausdorffIDist_closure, IMetric.hausdorffIDist_comm, Set.image_image]
        grw [IMetric.hausdorffIDist_image_le_of_le_sup, iSup₂_le (a := unitInterval.half^n)]
        · rfl
        · exact hbound
      · exact le_of_lt hn

    lemma φ_dense : DenseRange (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) := by
      intro y
      rcases y with v | ⟨⟩ | h
      · exact subset_closure ⟨⟨0, .inl v⟩, rfl⟩
      · exact subset_closure ⟨⟨0, .inr .unit⟩, rfl⟩
      · rw [mem_closure_iff_nhds']
        intro U hU
        obtain ⟨ε, hε, hball⟩ := IMetric.nhds_basis_ball.mem_iff.mp hU
        obtain ⟨n, hT⟩ := Closeds.Branch.approx_uniform h hε
        choose T hT' using hT
        exists ⟨φ ⟨n + 1, .inr (.inr (T ·))⟩, ?_⟩
        · grind only [= Set.mem_range]
        · apply hball
          rw [IMetric.mem_ball']

          apply LE.le.trans_lt (b := ε / 2)
          · erw [idist_comm, UniformFun.idist_eq_iSup]
            change (⨆ σ : «Σ», IMetric.hausdorffIDist (closure (Branch.map (embedAt n) '' T σ)) (h σ)).val ≤ ε / 2

            by_cases h : ε / 2 ≤ 1
            · have ge_zero : 0 ≤ ε / 2 := by linarith

              change _ ≤ (⟨ε / 2, ⟨ge_zero, h⟩⟩ : unitInterval)
              change ∀ σ, _ ≤ (⟨ε / 2, ⟨ge_zero, h⟩⟩ : unitInterval) at hT'

              apply iSup_le
              assumption
            · trans 1
              · apply unitInterval.le_one
              · apply le_of_not_ge h
          · exact half_lt_self hε

    theorem φ_isometry : Isometry (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) := by
      rintro ⟨m, p⟩ ⟨n, q⟩

      rw [edist_dist, edist_dist]
      change
        ENNReal.ofReal (idist (φ ⟨m, p⟩) (φ ⟨n, q⟩) : ℝ) =
        ENNReal.ofReal (idist (IterativeDomain.lift (le_max_left m n) p) (IterativeDomain.lift (le_max_right m n) q) : ℝ)
      congr 2

      cases m <;> cases n

      case zero.zero =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl

      case zero.succ =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl
        | IterativeDomain.leaf v, IterativeDomain.branch f => rfl
        | IterativeDomain.abort, IterativeDomain.branch f => rfl

      case succ.zero =>
        match q, p with
        | IterativeDomain.leaf v, IterativeDomain.leaf v' => rfl
        | IterativeDomain.abort, IterativeDomain.leaf v' => rfl
        | IterativeDomain.leaf v, IterativeDomain.abort => rfl
        | IterativeDomain.abort, IterativeDomain.abort => rfl
        | IterativeDomain.leaf v, IterativeDomain.branch f => rfl
        | IterativeDomain.abort, IterativeDomain.branch f => rfl

      case succ.succ m n =>
        match p, q with
        | IterativeDomain.leaf v, IterativeDomain.leaf v'
        | IterativeDomain.abort, IterativeDomain.leaf v'
        | IterativeDomain.leaf v, IterativeDomain.abort =>
          simp [φ]
        | IterativeDomain.abort, IterativeDomain.abort =>
          simp! only [φ]
          erw [IterativeDomain.lift_abort, IterativeDomain.lift_abort, IterativeDomain.idist_abort_abort]
          rfl
        | IterativeDomain.branch f, IterativeDomain.leaf v'
        | IterativeDomain.leaf v, IterativeDomain.branch g =>
          simp only [IterativeDomain.lift_leaf, IterativeDomain.idist_cast max_succ]
          push_cast
          rfl
        | IterativeDomain.branch f, IterativeDomain.abort
        | IterativeDomain.abort, IterativeDomain.branch g =>
          simp only [IterativeDomain.lift_abort, IterativeDomain.idist_cast max_succ]
          push_cast
          rfl
        | IterativeDomain.branch f, IterativeDomain.branch g =>
          simp only [IterativeDomain.idist_cast max_succ]
          push_cast
          repeat rw [IterativeDomain.lift_branch]

          change
            idist (α := «Σ» →ᵤ _) (λ σ ↦ (closure (Branch.map (embedAt m) '' f σ))) (_) =
            idist (α := «Σ» →ᵤ _) (λ σ ↦ Branch.map (IterativeDomain.lift _) '' f σ) (λ σ ↦ Branch.map (IterativeDomain.lift _) '' g σ)
          repeat erw [UniformFun.idist_eq_iSup]
          change
            ⨆ σ, IMetric.hausdorffIDist (closure (Branch.map (embedAt m) '' f σ)) (closure (Branch.map (embedAt n) '' g σ)) =
            ⨆ σ, IMetric.hausdorffIDist _ _

          let N := max m n

          congr 1; funext σ
          rw [IMetric.hausdorffIDist_closure]

          have h₁ :
              Branch.map (embedAt m : (IterativeDomain «Σ» Γ α β m).carrier → Domain «Σ» Γ α β) =
              Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (embedAt N) ∘ Branch.map (IterativeDomain.lift (le_max_left m n)) := by
            rw [Branch.map_comp, embedAt_comp_lift_eq (le_max_left m n)]

          have h₂ :
              Branch.map (embedAt n : (IterativeDomain «Σ» Γ α β n).carrier → Domain «Σ» Γ α β) =
              Branch.map («Σ» := «Σ») (Γ := Γ) (α := α) (embedAt N) ∘ Branch.map (IterativeDomain.lift (le_max_right m n)) := by
            rw [Branch.map_comp, embedAt_comp_lift_eq (le_max_right m n)]

          erw [h₁, h₂, Function.comp_def, ← Set.image_image, Function.comp_def, ← Set.image_image (s := g σ)]
          conv_lhs =>
            apply IMetric.hausdorffIDist_image (Φ := Branch.map (embedAt N)) (Branch.map_isometry embedAt_isometry)

    theorem φ_uniform_continuous : UniformContinuous (φ («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) :=
      φ_isometry.uniformContinuous

    section
      variable
        {«Σ» : Type u} {Γ : Type v} {α : Type w} {β : Type x} {γ : Type y} {δ : Type z}
        [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace β]
        [CompleteSpace «Σ»] [CompleteSpace Γ] [CompleteSpace α] [CompleteSpace β]

      /--
        We establish the equivalence in order to prove that our defined domain is a solution
        to the original equation.
      -/
      def Domain.isSolution :
          Domain «Σ» Γ α β ≃ᵢ β ⊕ PUnit.{x + 1} ⊕ («Σ» →ᵤ Closeds (Branch «Σ» Γ α (Domain «Σ» Γ α β))) :=
        let h := UniformSpace.Completion.extension φ

        have h_iso : Isometry h := Isometry.completion_extension φ_isometry

        have h_antilipschitz := h_iso.antilipschitz

        have h_uniform_continuous := h_iso.uniformContinuous

        have h_complete_range := h_antilipschitz.isComplete_range h_uniform_continuous

        have h_closed_range := h_complete_range.isClosed

        have h_dense : DenseRange h := by
          apply Dense.mono
          · exact Set.range_comp_subset_range ((↑) : DomainUnion «Σ» Γ α β → UniformSpace.Completion _) h
          · unfold h
            rw [Function.comp_def]
            conv => enter [1, 1, x]; rw [UniformSpace.Completion.extension_coe φ_uniform_continuous]
            apply φ_dense

        have h_surj : Function.Surjective h := λ x ↦ by
          have h : x ∈ closure (Set.range h) := h_dense x
          rwa [h_closed_range.closure_eq] at h

        IsometryEquiv.mk
          (Equiv.ofBijective h ⟨h_iso.injective, h_surj⟩)
          h_iso

      def Domain.abort : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inr (.inl .unit))

      def Domain.leaf (v : β) : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inl v)

      def Domain.branch (f : «Σ» →ᵤ Set (Branch «Σ» Γ α (Domain «Σ» Γ α β))) : Domain «Σ» Γ α β :=
        ⇑Domain.isSolution.symm (.inr (.inr λ σ ↦ ⟨closure (f σ), isClosed_closure⟩))

      theorem Domain.idist_leaf_leaf {v v' : β} :
          idist (Domain.leaf («Σ» := «Σ») (Γ := Γ) (α := α) v) (Domain.leaf v') = idist v v' := by
        unfold Domain.leaf
        rw [Isometry.to_idist_eq (IsometryEquiv.isometry _)]

      theorem Domain.idist_abort_abort :
          idist (Domain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)) Domain.abort = ⊥ := by
        unfold Domain.abort
        rw [Isometry.to_idist_eq (IsometryEquiv.isometry _)]
        rfl

      theorem Domain.idist_branch_branch {f f' : «Σ» →ᵤ Set (Branch «Σ» Γ α (Domain «Σ» Γ α β))} :
          idist (Domain.branch f) (Domain.branch f') = ⨆ σ, idist (f σ) (f' σ) := by
        unfold Domain.branch
        erw [Isometry.to_idist_eq (IsometryEquiv.isometry _), UniformFun.idist_eq_iSup]
        apply iSup_congr λ σ ↦ ?_
        rw [Closeds.idist_eq]
        change IMetric.hausdorffIDist (closure _) (closure _) = _
        rw [IMetric.hausdorffIDist_closure]

      instance : Nonempty (Domain «Σ» Γ α β) := .intro .abort

      theorem Domain.isOpen_singleton_abort :
          IsOpen {Domain.abort («Σ» := «Σ») (Γ := Γ) (α := α) (β := β)} := by
        unfold Domain.abort
        rw [← IsometryEquiv.coe_toHomeomorph_symm, ← Set.image_singleton, Homeomorph.isOpen_image,
            isOpen_sum_iff, isOpen_sum_iff]
        and_intros
        · convert isOpen_empty
          grind only [= Set.mem_empty_iff_false, = Set.mem_preimage, = Set.mem_singleton_iff]
        · convert isOpen_discrete {PUnit.unit}
          · rfl
          · grind only [= Set.mem_singleton_iff, = Set.mem_preimage]
        · convert isOpen_empty
          grind only [= Set.mem_empty_iff_false, = Set.mem_preimage, = Set.mem_singleton_iff]

      theorem Domain.exists_abort_eq :
          ∃ n, (Domain.abort : Domain «Σ» Γ α β) = UniformSpace.Completion.coe' (DomainUnion.mk (n := n) IterativeDomain.abort) := by
        convert_to ∃ n, isSolution abort = isSolution (UniformSpace.Completion.coe' (DomainUnion.mk (n := n) IterativeDomain.abort)) using 0
        · apply exists_congr
          intros n
          iff_intro h h
          · apply_fun isSolution at h
            assumption
          · apply_fun isSolution
            assumption
        · unfold abort
          change ∃ n, _ = UniformSpace.Completion.extension φ _
          rw [IsometryEquiv.apply_symm_apply]
          conv => enter [1, n]; rw [UniformSpace.Completion.extension_coe φ_uniform_continuous]
          exists 0

      theorem Domain.coe_eq_abort_iff {p : DomainUnion «Σ» Γ α β} :
          (p : Domain «Σ» Γ α β) = Domain.abort ↔ ∃ n, p = ⟨n, IterativeDomain.abort⟩ := by
        iff_rintro p_eq ⟨n, rfl⟩
        · apply_fun isSolution at p_eq
          change UniformSpace.Completion.extension φ (p : Domain «Σ» Γ α β) = isSolution abort at p_eq
          erw [UniformSpace.Completion.extension_coe, IsometryEquiv.apply_symm_apply] at p_eq
          · let ⟨n, p⟩ := p
            match n, p with
            | 0, IterativeDomain.abort =>
              exists 0
            | n + 1, IterativeDomain.abort =>
              exists n + 1
            | 0, IterativeDomain.leaf v | n + 1, IterativeDomain.leaf v
            | n + 1, IterativeDomain.branch f =>
              injections
          · exact φ_uniform_continuous
        · apply_fun isSolution
          change UniformSpace.Completion.extension φ _ = isSolution (isSolution.symm _)
          erw [UniformSpace.Completion.extension_coe, IsometryEquiv.apply_symm_apply]
          · cases n with rfl
          · exact φ_uniform_continuous

      theorem Domain.coe_eq_branch_iff {p : DomainUnion «Σ» Γ α β} {f : «Σ» → Set (Branch «Σ» Γ α (Domain «Σ» Γ α β))} :
          (p : Domain «Σ» Γ α β) = Domain.branch f ↔ ∃ m g, p = ⟨m + 1, IterativeDomain.branch g⟩ ∧ ∀ σ, closure (Branch.map (embedAt m) '' g σ) = closure (f σ) := by
        iff_rintro p_eq ⟨n, g, rfl, g_eq⟩
        · apply_fun isSolution at p_eq
          change UniformSpace.Completion.extension φ _ = isSolution (isSolution.symm _) at p_eq
          erw [UniformSpace.Completion.extension_coe, IsometryEquiv.apply_symm_apply] at p_eq
          · let ⟨m, p⟩ := p
            match m, p with
            | 0, IterativeDomain.abort | m + 1, IterativeDomain.abort
            | 0, IterativeDomain.leaf v | m + 1, IterativeDomain.leaf v =>
              injections
            | m + 1, IterativeDomain.branch g =>
              injections _ g_eq
              conv at g_eq =>
                rw [funext_iff]
                enter [σ]
                erw [Closeds.ext_iff]
                dsimp [Function.comp_def]

              exists m, g
          · exact φ_uniform_continuous
        · apply_fun isSolution
          change UniformSpace.Completion.extension φ _ = isSolution (isSolution.symm _)
          erw [UniformSpace.Completion.extension_coe, IsometryEquiv.apply_symm_apply]
          · dsimp [φ]
            congr 2 with σ : 1
            congr 1
            exact g_eq σ
          · exact φ_uniform_continuous
    end
  end




  namespace Value
    variable
      {«Σ» : Type u} {Γ : Type v} {α : Type w} {β : Type x} {γ : Type y} {δ : Type z}
      [IMetricSpace «Σ»] [DecidableEq Γ] [DiscreteIMetricSpace Γ] [IMetricSpace α] [IMetricSpace β] [IMetricSpace γ]
    variable (Γ «Σ»)
    variable (ℍ : Type y) (Typ : Type w) [IMetricSpace ℍ] [IMetricSpace Typ]

    /--
      The type of values that can be sent through channels.
    -/
    inductive Send𝕍 : Type (max w y) where
      | bool (b : Bool)
      | int (n : ℤ)
      | str (s : String)
      | slice (cap low high : ℕ) (arr : ℍ)
      | chan (len : ℍ) (τ : Typ) (arr closed? : ℍ)
      | struct (fields : AList λ _ : String ↦ ℍ)
      | array (len : ℕ) (indices : Fin len → ℍ)
      | map (fields : List (Sigma λ _ : Send𝕍 ↦ ℍ)) (nil : Bool)
      | tuple (fields : List Send𝕍)

    instance : DecidableEq (Send𝕍 ℍ Typ) :=
      sorry

    instance : DiscreteIMetricSpace (Send𝕍 ℍ Typ) where
      __ := IMetricSpace.discrete
    instance : CompleteSpace (Value.Send𝕍 ℍ Typ) :=
      DiscreteIMetricSpace.completeSpace

    protected abbrev F (𝕍 : Type x) [IMetricSpace 𝕍] : Type (max u v w x y) :=
      -- bool
        Bool
      -- int
      ⊕ ℤ
      -- str
      ⊕ String
      -- slice
      ⊕ ℕ × ℕ × ℕ × ℍ
      -- chan
      ⊕ ℍ × Typ × ℍ × ℍ
      -- struct
      ⊕ (String →ᵤ Option ℍ)
      -- array
      ⊕ (Σ n : ℕ, Fin n →ᵤ ℍ)
      -- map
      ⊕ (Restriction 𝕍 unitInterval.half →ᵤ Option ℍ) × Bool
      -- func
      ⊕ (List ℍ × List Γ →ᵤ Domain «Σ» Γ (Send𝕍 ℍ Typ) PUnit.{x + 1})
      -- tuples
      ⊕ List (Restriction 𝕍 unitInterval.half)

    variable {«Σ» Γ ℍ Typ}

    -- `Value.F`'s `PseudoEMetricSpace` instance (via `IMetricSpace`) needs decidability of
    -- equality on the abstract `ℍ`/`Typ`/`Γ` parameters throughout this section — every
    -- concrete instantiation below (`𝕍_iso`, `casesOn`, …) re-triggers the same synthesis.
    set_option linter.style.openClassical false
    open Classical

    instance {𝕍 : Type u} [IMetricSpace 𝕍] : IMetricSpace (Value.F «Σ» Γ ℍ Typ 𝕍) :=
      inferInstance

    /-!
      `𝕍` is constructed similarly to `Domain`.
      This is painful, and we know that it will work.

      For now, let's just axiomatize `𝕍`. We know it exists (from various results
      of domain theory), we just don't construct them yet.
      `𝕍` is just very cumbersome to define and construct. We'll leave this as
      future work for now.
    -/
    axiom 𝕍 («Σ» : Type u) (Γ : Type v) (ℍ : Type w) (Typ : Type x) : NonemptyType.{max u v w x}

    instance : Nonempty (𝕍 «Σ» Γ ℍ Typ).type := (𝕍 ..).property

    @[instance]
    axiom 𝕍_metricSpace : IMetricSpace (𝕍 «Σ» Γ ℍ Typ).type

    /--
      Axiomatize the fact that `𝕍` is a solution to the recursive domain
      equation `𝕍 = F(𝕍)`.
    -/
    axiom 𝕍_iso : (𝕍 «Σ» Γ ℍ Typ).type ≃ᵢ Value.F «Σ» Γ ℍ Typ (𝕍 «Σ» Γ ℍ Typ).type

    @[instance]
    axiom 𝕍_complete : CompleteSpace (𝕍 «Σ» Γ ℍ Typ).type

    axiom 𝕍_isSend : (𝕍 «Σ» Γ ℍ Typ).type → Prop

    @[instance]
    axiom 𝕍_isSend_decidable {v : (𝕍 «Σ» Γ ℍ Typ).type} : Decidable (𝕍_isSend v)

    axiom 𝕍_extract (v : (𝕍 «Σ» Γ ℍ Typ).type) (isSend : 𝕍_isSend v) : Send𝕍 ℍ Typ



    def 𝕍.bool (b : Bool) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inl b)

    def 𝕍.int (n : ℤ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inl n)

    def 𝕍.str (s : String) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inl s)

    def 𝕍.slice (cap low high : ℕ) (array : ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inl ⟨cap, low, high, array⟩)

    def 𝕍.chan (length : ℍ) (τ : Typ) (array closed : ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inl ⟨length, τ, array, closed⟩)

    def 𝕍.struct (fields : String →ᵤ Option ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inl fields)

    def 𝕍.array (len : ℕ) (indices : Fin len →ᵤ ℍ) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨len, indices⟩)

    def 𝕍.map (maps : (𝕍 «Σ» Γ ℍ Typ).type →ᵤ Option ℍ) (isNil : Bool) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨maps ∘ Restriction.val, isNil⟩)

    def 𝕍.func (call : List ℍ × List Γ →ᵤ Domain «Σ» Γ (Send𝕍 ℍ Typ) PUnit) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl (λ ⟨vs, ξ⟩ ↦ call ⟨vs, ξ⟩))

    def 𝕍.tuple (vs : List (𝕍 «Σ» Γ ℍ Typ).type) : (𝕍 «Σ» Γ ℍ Typ).type :=
      𝕍_iso.symm (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr vs)


    axiom 𝕍_isSend.tuple {vs : List (𝕍 «Σ» Γ ℍ Typ).type} (h : ∀ v ∈ vs, 𝕍_isSend v) : 𝕍_isSend (𝕍.tuple vs)


    @[cases_eliminator]
    noncomputable def 𝕍.casesOn {motive : (𝕍 «Σ» Γ ℍ Typ).type → Sort _}
      (bool : ∀ b, motive (𝕍.bool b))
      (int : ∀ n, motive (𝕍.int n))
      (str : ∀ s, motive (𝕍.str s))
      (slice : ∀ cap low high array, motive (𝕍.slice cap low high array))
      (chan : ∀ len τ array closed, motive (𝕍.chan len τ array closed))
      (struct : ∀ fields, motive (𝕍.struct fields))
      (array : ∀ len indices, motive (𝕍.array len indices))
      (map : ∀ maps isNil, motive (𝕍.map maps isNil))
      (func : ∀ call, motive (𝕍.func call))
      (tuple : ∀ vs, motive (𝕍.tuple vs))
      (v : (𝕍 «Σ» Γ ℍ Typ).type) :
        motive v :=
      match h : 𝕍_iso v with
      | .inl b =>
        have h' : v = 𝕍.bool b := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ bool b
      | .inr (.inl n) =>
        have h' : v = 𝕍.int n := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ int n
      | .inr (.inr (.inl s)) =>
        have h' : v = 𝕍.str s := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ str s
      | .inr (.inr (.inr (.inl ⟨cap, low, high, array⟩))) =>
        have h' : v = 𝕍.slice cap low high array := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ slice cap low high array
      | .inr (.inr (.inr (.inr (.inl ⟨length, τ, array, closed⟩)))) =>
        have h' : v = 𝕍.chan length τ array closed := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ chan length τ array closed
      | .inr (.inr (.inr (.inr (.inr (.inl fields))))) =>
        have h' : v = 𝕍.struct fields := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ struct fields
      | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨len, indices⟩)))))) =>
        have h' : v = 𝕍.array len indices := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ array len indices
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨maps, isNil⟩))))))) =>
        have h' : v = 𝕍.map (maps ∘ Restriction.mk) isNil := by
          apply_fun 𝕍_iso.symm at h
          rwa [IsometryEquiv.symm_apply_apply] at h
        h' ▸ map (maps ∘ Restriction.mk) isNil
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl call)))))))) =>
        have h' : v = 𝕍.func (λ ⟨vs, ξ⟩ ↦ call ⟨vs, ξ⟩) := by
          apply_fun 𝕍_iso.symm at h
          rw [IsometryEquiv.symm_apply_apply] at h
          rw [h, 𝕍.func]
        h' ▸ func (λ ⟨vs, ξ⟩ ↦ call ⟨vs, ξ⟩)
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr vs)))))))) =>
        have h' : v = 𝕍.tuple (List.map Restriction.val vs) := by
          apply_fun 𝕍_iso.symm at h
          rw [IsometryEquiv.symm_apply_apply] at h
          rewrite [h, 𝕍.tuple, ← List.map_eq_map, bind_map_left]
          simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_singleton']
        h' ▸ tuple (List.map Restriction.val vs)
  end Value
end Domain

end
