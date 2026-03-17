import Extra.Topology.IMetricSpace

universe u v

noncomputable instance {α : Type u} {β : Type v} [Nonempty α] [IMetricSpace β] : IMetricSpace (α → β) where
  idist f g := ⨆ x : α, idist (f x) (g x) -- uniform distance
  idist_self f := by
    conv_lhs => enter [1, x]; rw [idist_self]
    rw [iSup_const]
  idist_comm f g := by
    conv_lhs => enter [1, x]; rw [idist_comm]
  idist_triangle f g h := by
    admit
  eq_of_idist_eq_zero {f g} h := by
    erw [iSup_eq_bot] at h
    replace h : ∀ (i : α), f i = g i := λ i ↦ eq_of_idist_eq_zero _ _ (h i)
    exact funext h
  toUniformSpace := Pi.uniformSpace (λ _ ↦ β)
  uniformity_idist := by
    admit

-- instance {α : Type u} {β : Type v} [UniformSpace β] : UniformSpace (α → β) :=
--   Pi.uniformSpace (λ _ ↦ β)

instance {α : Type u} {β : Type v} [UniformSpace β] [CompleteSpace β] : CompleteSpace (α → β) :=
  Pi.complete (λ _ ↦ β)
