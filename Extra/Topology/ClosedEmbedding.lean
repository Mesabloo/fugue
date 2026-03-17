import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic

structure ClosedEmbedding (α β) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  isClosedEmbedding : Topology.IsClosedEmbedding toFun
infixr:25 " ↪c " => ClosedEmbedding

instance {α β} [TopologicalSpace α] [TopologicalSpace β] : Coe (ClosedEmbedding α β) (α → β) :=
  ⟨ClosedEmbedding.toFun⟩
