import PoincareConjecture.Definitions.M36MetricSurgery








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




structure RepairedMetricSurgeryTheory : Prop where
  surgery : ∀ g₀ : StandardInitialMetric,
    Nonempty (RepairedMetricSurgeryData.{u} g₀)

end PoincareConjecture
