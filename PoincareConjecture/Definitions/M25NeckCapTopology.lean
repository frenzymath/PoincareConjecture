import PoincareConjecture.Statements.Ch09.NeckCapTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure RepairedNeckCapTopologyData
    (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g) where
  region : NeckCapRegion g H.X
  compatible : NeckCapRegionCompatible g H region

end PoincareConjecture
