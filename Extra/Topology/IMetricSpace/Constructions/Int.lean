module
public import Extra.Topology.IMetricSpace
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Instances.Int

public section

noncomputable instance : IMetricSpace ℕ := .transportMetricSpace

noncomputable instance : IMetricSpace ℤ := .transportMetricSpace

end
