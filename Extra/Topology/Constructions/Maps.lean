module
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Basic
public import Extra.Topology.ClosedEmbedding
public import Extra.Topology.IMetricSpace
public import Extra.Topology.IMetricSpace.Constructions.Function

attribute [-instance] UniformFun.instPseudoEMetricSpace UniformFun.instEMetricSpace

public section

lemma Set.range_const' {α β} [Nonempty α] {v : β} : Set.range (Function.const α v) = {v} := by
  unfold Set.range
  grind only [usr mem_setOf_eq, = mem_singleton_iff]

open scoped UniformConvergence

@[ext]
theorem UniformFun.ext {α β} {f g : α →ᵤ β} (h : ∀ x, f x = g x) : f = g := funext h

@[expose]
def UniformFun.map {α β γ} (g : β → γ) (f : α →ᵤ β) : α →ᵤ γ := g ∘ f

theorem UniformFun.map_apply {α β γ} {g : β → γ} {f : α →ᵤ β} {x : α} :
    UniformFun.map g f x = g (f x) := by
  unfold UniformFun.map
  rfl

protected theorem UniformFun.map_isometry' {α β γ} [PseudoIMetricSpace β] [PseudoIMetricSpace γ]
  {g : β → γ} (hg : ∀ x y, idist (g x) (g y) = idist x y) :
    ∀ (f f' : α →ᵤ β), idist (UniformFun.map g f) (UniformFun.map g f') = idist f f' := by
  intro f f'
  apply_fun Subtype.val
  · rw [UniformFun.idist_eq, UniformFun.idist_eq]
    congr 1
    simp only [UniformFun.edist_def, UniformFun.map, edist_dist]
    congr 1 with x
    congr 1
    exact congr_arg Subtype.val (hg (f x) (f' x))
  · exact Subtype.val_injective

protected theorem UniformFun.map_isometry {α β γ} {g : β → γ} [PseudoIMetricSpace β] [PseudoIMetricSpace γ]
  (hg : Isometry g) :
    Isometry (UniformFun.map (α := α) g) := by
  apply Isometry.of_idist_eq
  apply UniformFun.map_isometry'
  apply Isometry.to_idist_eq
  exact hg

theorem UniformFun.uniformContinuous_map {ι α β} {f : α →ᵤ β} [UniformSpace α] [UniformSpace β]
  (hf : UniformContinuous f) :
    UniformContinuous (UniformFun.map (α := ι) f) :=
  UniformFun.postcomp_uniformContinuous hf

theorem Pi.uniformContinuous_map_const {ι α β} {f : α →ᵤ β} [UniformSpace α] [UniformSpace β]
  (hf : UniformContinuous f) :
    UniformContinuous (Pi.map λ _ : ι ↦ f) := by
  rw [uniformContinuous_pi]
  intro _
  apply UniformContinuous.comp
  · exact hf
  · apply uniformContinuous_proj

end
