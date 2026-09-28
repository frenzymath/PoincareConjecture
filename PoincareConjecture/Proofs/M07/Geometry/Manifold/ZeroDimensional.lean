import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.TotallyDisconnected

namespace Poincare

theorem subsingleton_of_preconnected_chartedSpace
    (H M : Type*) [TopologicalSpace H] [DiscreteTopology H]
    [TopologicalSpace M] [ChartedSpace H M] [PreconnectedSpace M] :
    Subsingleton M := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology H M
  exact subsingleton_of_preconnected_totallyDisconnected

theorem subsingleton_of_preconnected_euclidean_zero
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [PreconnectedSpace M] :
    Subsingleton M :=
  subsingleton_of_preconnected_chartedSpace (EuclideanSpace ℝ (Fin 0)) M

end Poincare
