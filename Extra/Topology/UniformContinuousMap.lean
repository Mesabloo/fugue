import Mathlib.Topology.UniformSpace.Defs

structure UniformContinuousMap (α β) [UniformSpace α] [UniformSpace β] where
  toFun : α → β
  isUniformContinuous : UniformContinuous toFun

notation "UC(" α ", " β ")" => UniformContinuousMap α β

instance {α β} [UniformSpace α] [UniformSpace β] : FunLike UC(α, β) α β where
  coe := UniformContinuousMap.toFun
  coe_injective' := λ ⟨_, _⟩ ⟨_, _⟩ h ↦ by
    grind only
