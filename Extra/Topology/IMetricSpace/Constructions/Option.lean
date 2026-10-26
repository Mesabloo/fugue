module
public import Extra.Topology.IMetricSpace
public import Extra.Topology.IMetricSpace.Constructions.Sum

public section

def Option.toSum.{u} {α : Type u} : Option α → PUnit.{u + 1} ⊕ α
  | .none => .inl .unit
  | .some x => .inr x

theorem Option.toSum_injective {α} : Function.Injective (Option.toSum (α := α)) := by
  rintro (_|x) (_|y) <;> grind only [= toSum]

theorem Option.toSum_surjective {α} : Function.Surjective (Option.toSum (α := α)) := by
  rintro (_|x)
  · exists .none
  · exists .some x

instance : IMetricSpace PUnit := .of_metric_space_of_dist_le_one
instance (priority := high) : CompleteSpace PUnit := inferInstance
instance : DiscreteIMetricSpace PUnit where

instance {α} [IMetricSpace α] : IMetricSpace (Option α) :=
  .induced _ Option.toSum_injective inferInstance
  /- idist
   -   | .none, .none => ⊥
   -   | .some x, .some y => idist x y
   -   | .some _, .none | .none, .some _ => ⊤
   - idist_self x := by cases x <;> first | rfl | grind only [idist_self]
   - idist_comm x y := by
   -   cases x <;> cases y <;> first | rfl | grind only [idist_comm]
   - idist_triangle x y z := by
   -   cases x <;> cases y <;> cases z <;>
   -     grind only [= Set.mem_Icc, unitInterval.bot_eq, unitInterval.coe_ne_one, unitInterval.coe_ne_zero,
   -       unitInterval.top_eq, idist_triangle]
   - eq_of_idist_eq_zero {x y} h := by
   -   split at h <;> grind only [eq_of_idist_eq_zero, unitInterval.coe_ne_one, unitInterval.coe_ne_zero, unitInterval.top_eq] -/

theorem Option.toSum_is_uniform_inducing {α} [IMetricSpace α] : IsUniformInducing (Option.toSum (α := α)) := ⟨rfl⟩

instance {α} [IMetricSpace α] [CompleteSpace α] : CompleteSpace (Option α) :=
  IsUniformInducing.completeSpace (f := Option.toSum) Option.toSum_is_uniform_inducing <| by
    have : Set.range (Option.toSum (α := α)) = Set.univ := by
      rw [← Set.image_univ, Set.image_univ_of_surjective]
      exact Option.toSum_surjective
    rw [this]
    apply complete_univ

end
