import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected zero-dimensional manifolds

A charted space over a discrete model is discrete, so preconnectedness makes
its carrier subsingleton. The Euclidean dimension-zero specialization handles
the carrier in the dimension-zero case of pointed Ricci-flow compactness
(Morgan--Tian, Theorem 5.15, printed pp. 91--92).
-/

namespace Poincare

/-- A preconnected charted space over a discrete model has at most one point. -/
theorem subsingleton_of_preconnected_chartedSpace
    (H M : Type*) [TopologicalSpace H] [DiscreteTopology H]
    [TopologicalSpace M] [ChartedSpace H M] [PreconnectedSpace M] :
    Subsingleton M := by
  let : DiscreteTopology M := ChartedSpace.discreteTopology H M
  exact subsingleton_of_preconnected_totallyDisconnected

/-- A preconnected manifold modeled on zero-dimensional Euclidean space has
at most one point. No differentiability or separation assumption is needed. -/
theorem subsingleton_of_preconnected_euclidean_zero
    (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [PreconnectedSpace M] :
    Subsingleton M :=
  subsingleton_of_preconnected_chartedSpace (EuclideanSpace ℝ (Fin 0)) M

end Poincare
