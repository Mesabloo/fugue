import Extra.Topology.IMetricSpace

instance Prod.instIMetricSpace {α β} [IMetricSpace α] [IMetricSpace β] : IMetricSpace (α × β) :=
  .of_metric_space_of_dist_le_one λ x y ↦ by
    change max (idist x.1 y.1) (idist x.2 y.2) ≤ 1
    apply max_le
    · exact unitInterval.le_one'
    · exact unitInterval.le_one'
