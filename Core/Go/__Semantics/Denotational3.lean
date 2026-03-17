import Extra.List
import Mathlib.Data.Nat.Lattice
import CustomPrelude
import Extra.Nat
import Extra.AList
import Core.Go.Syntax
import Extra.Fin
import Extra.List
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Maps.Basic
import Extra.Topology.Constructions.SumProd
import Extra.Topology.IMetricSpace.Constructions
import Extra.Topology.ClosedEmbedding

class abbrev CompleteIMetricSpace (α : Type _) := IMetricSpace α, CompleteSpace α

structure Object.{u} where
  carrier : Type u
  [completeMetricSpace : CompleteIMetricSpace carrier]

instance {o : Object} : CompleteIMetricSpace o.carrier := o.completeMetricSpace

section Domain
  universe u v w x y z
  variable («Σ» : Type u) (Γ : Type v) (α : Type w) (β : Type x) (γ : Type y) (δ : Type z)

  def Branch :=
      (Γ × (α → Bool → Restriction γ unitInterval.half))
    ⊕ (Γ × α × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ (Γ × Restriction γ unitInterval.half)
    ⊕ («Σ» × Restriction γ unitInterval.half)

  section Branch
    variable {«Σ» Γ α β γ δ}

    @[match_pattern]
    protected abbrev Branch.recv (c : Γ) (π : α → Bool → γ) : Branch «Σ» Γ α γ := .inl (c, π)
    @[match_pattern]
    protected abbrev Branch.send (c : Γ) (v : α) (p : γ) : Branch «Σ» Γ α γ := .inr (.inl (c, v, p))
    @[match_pattern]
    protected abbrev Branch.close (c : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inl (c, p)))
    @[match_pattern]
    protected abbrev Branch.sync (c : Γ) (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inl (c, p))))
    @[match_pattern]
    protected abbrev Branch.next (σ : «Σ») (p : γ) : Branch «Σ» Γ α γ := .inr (.inr (.inr (.inr (σ, p))))

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

    noncomputable instance Branch.instIMetricSpace [Nonempty α] [IMetricSpace «Σ»] [IMetricSpace Γ] [IMetricSpace α] [IMetricSpace γ] :
        IMetricSpace (Branch «Σ» Γ α γ) :=
      Sum.instIMetricSpace

    instance Branch.instCompleteSpace [Nonempty α] [CompleteIMetricSpace «Σ»] [CompleteIMetricSpace Γ] [CompleteIMetricSpace α] [CompleteIMetricSpace γ] :
        CompleteSpace (Branch «Σ» Γ α γ) :=
      inferInstanceAs (CompleteSpace (_ ⊕ _ ⊕ _ ⊕ _ ⊕ _))
  end Branch

  variable [Nonempty «Σ»] [Nonempty α] [CompleteIMetricSpace β] [CompleteIMetricSpace «Σ»] [CompleteIMetricSpace Γ] [CompleteIMetricSpace α]

  open TopologicalSpace (Closeds)

  instance : IMetricSpace PUnit.{u + 1} := .of_metric_space_of_dist_le_one

  -- set_option pp.explicit true in
  private noncomputable def IterativeDomain : ℕ → Object.{max u v w x}
    | 0 => { carrier := β ⊕ PUnit.{max u v w + 1} }
    | n + 1 => { carrier := β ⊕ PUnit.{u + 1} ⊕ («Σ» → Closeds (Branch «Σ» Γ α (IterativeDomain n).carrier)) }

  noncomputable def DomainUnion : Object where
    carrier := Σ n, (IterativeDomain «Σ» Γ α β n).carrier

  noncomputable abbrev Domain := UniformSpace.Completion (DomainUnion «Σ» Γ α β).carrier

  noncomputable instance : MetricSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.instMetricSpace

  instance : CompleteSpace (Domain «Σ» Γ α β) :=
    UniformSpace.Completion.completeSpace _

  variable {«Σ» Γ α β γ δ} [CompleteIMetricSpace γ]

  section Operators
    section Map
      /-! ## Functorial mapping -/

      noncomputable def Branch.map {γ'} [CompleteIMetricSpace γ'] (g : γ ↪c γ') :
          (Branch «Σ» Γ α γ) ↪c (Branch «Σ» Γ α γ') where
        toFun :=
          Sum.map (Prod.map id (Pi.map λ _ ↦ Pi.map λ _ ↦ Restriction.map g.toFun)) <|
          Sum.map (Prod.map id (Prod.map id (Restriction.map g.toFun))) <|
          Sum.map (Prod.map id (Restriction.map g.toFun)) <|
          Sum.map (Prod.map id (Restriction.map g.toFun))
                  (Prod.map id (Restriction.map g.toFun))
        isClosedEmbedding := by
          apply Topology.IsClosedEmbedding.sumMap
          · apply Topology.IsClosedEmbedding.prodMap
            · exact Topology.IsClosedEmbedding.id
            · refine Topology.IsClosedEmbedding.piMap λ _ ↦ ?_
              refine Topology.IsClosedEmbedding.piMap λ _ ↦ ?_
              apply Restriction.map.isClosedEmbedding
              exact g.isClosedEmbedding
          · apply Topology.IsClosedEmbedding.sumMap
            · apply Topology.IsClosedEmbedding.prodMap
              · exact Topology.IsClosedEmbedding.id
              · apply Topology.IsClosedEmbedding.prodMap
                · exact Topology.IsClosedEmbedding.id
                · apply Restriction.map.isClosedEmbedding
                  exact g.isClosedEmbedding
            · apply Topology.IsClosedEmbedding.sumMap
              · apply Topology.IsClosedEmbedding.prodMap
                · exact Topology.IsClosedEmbedding.id
                · apply Restriction.map.isClosedEmbedding
                  exact g.isClosedEmbedding
              · apply Topology.IsClosedEmbedding.sumMap
                · apply Topology.IsClosedEmbedding.prodMap
                  · exact Topology.IsClosedEmbedding.id
                  · apply Restriction.map.isClosedEmbedding
                    exact g.isClosedEmbedding
                · apply Topology.IsClosedEmbedding.prodMap
                  · exact Topology.IsClosedEmbedding.id
                  · apply Restriction.map.isClosedEmbedding
                    exact g.isClosedEmbedding

      noncomputable def IterativeDomain.map {β'} [CompleteIMetricSpace β'] (f : β ↪c β') {n} :
          (IterativeDomain «Σ» Γ α β n).carrier ↪c (IterativeDomain «Σ» Γ α β' n).carrier := match n with
        | 0 => {
          toFun := Sum.map f.toFun id
          isClosedEmbedding := by
            apply Topology.IsClosedEmbedding.sumMap
            · exact f.isClosedEmbedding
            · exact Topology.IsClosedEmbedding.id
        }
        | n + 1 => {
          toFun := Sum.map f.toFun <| Sum.map id <| Pi.map λ _ ↦ Closeds.map _ (Branch.map (IterativeDomain.map f)).isClosedEmbedding
          isClosedEmbedding := by
            apply Topology.IsClosedEmbedding.sumMap
            · exact f.isClosedEmbedding
            · apply Topology.IsClosedEmbedding.sumMap
              · exact Topology.IsClosedEmbedding.id
              · refine Topology.IsClosedEmbedding.piMap λ σ ↦ ?_
                apply Topology.IsClosedEmbedding.Closeds.map
        }

      noncomputable def Domain.map {β'} [CompleteIMetricSpace β'] (f : β ↪c β') :
          Domain «Σ» Γ α β → Domain «Σ» Γ α β' :=
        UniformSpace.Completion.map <| Sigma.map id λ _ ↦ (IterativeDomain.map f).toFun
    end Map

    section Ap

    end Ap

    section Bind
      -- noncomputable def Domain.bind
    end Bind
  end Operators
end Domain
