import PoincareLib.Geometry.Riemannian.Covering.Completeness
import PoincareLib.Topology.Manifold.NeckCap.Fibration.UniversalCover

/-!
# Completeness on the canonical smooth universal cover

This applies arbitrary-covering completeness to the existing universal-cover
atlas. No finiteness condition on the fundamental group is needed.

Application: Morgan--Tian, Proposition 9.83, p. 236.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Topology.UniversalCover

/-- The canonical universal cover, with its existing lifted atlas and the
differential pullback of a complete base metric, is complete. -/
theorem metricComplete_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [PathConnectedSpace M] [LocallyPathConnectedSpace M]
    [SemilocallySimplyConnectedSpace M]
    (g : PoincareMT.RiemannianMetric 3 M) (x₀ : M)
    (hc : PoincareMT.MetricComplete g) :
    letI := chartedSpace x₀
    letI := isManifold x₀
    letI := t3Space x₀
    PoincareMT.MetricComplete
      (g.pullbackOfLocalDiffeomorph (proj (x₀ := x₀)) (isLocalDiffeomorph x₀)) := by
  let := chartedSpace x₀
  let := isManifold x₀
  let := t3Space x₀
  exact g.metricComplete_pullbackOfLocalDiffeomorph _
    (isLocalDiffeomorph x₀) (isCoveringMap x₀) hc

end Poincare.Topology.UniversalCover
