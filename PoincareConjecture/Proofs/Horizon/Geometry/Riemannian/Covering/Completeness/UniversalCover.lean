import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Covering.Completeness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.UniversalCover

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Topology.UniversalCover

theorem metricComplete_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [PathConnectedSpace M] [LocallyPathConnectedSpace M]
    [SemilocallySimplyConnectedSpace M]
    (g : PoincareConjecture.RiemannianMetric 3 M) (x₀ : M)
    (hc : PoincareConjecture.MetricComplete g) :
    letI := chartedSpace x₀
    letI := isManifold x₀
    letI := t3Space x₀
    PoincareConjecture.MetricComplete
      (g.pullbackOfLocalDiffeomorph (proj (x₀ := x₀)) (isLocalDiffeomorph x₀)) := by
  let := chartedSpace x₀
  let := isManifold x₀
  let := t3Space x₀
  exact g.metricComplete_pullbackOfLocalDiffeomorph _
    (isLocalDiffeomorph x₀) (isCoveringMap x₀) hc

end Poincare.Topology.UniversalCover
