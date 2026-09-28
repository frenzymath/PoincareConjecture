import PoincareConjecture.Definitions.Ch01.Normalization
import PoincareConjecture.Statements.Ch04.Pinching










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

structure NormalizedInitialMetricConclusion where
  data : NormalizedInitialMetric (M := M)
  initial_pinching : HamiltonIveyPinchedAt data.connection 0

end PoincareConjecture
