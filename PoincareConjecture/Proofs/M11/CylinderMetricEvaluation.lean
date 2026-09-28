import PoincareConjecture.Proofs.M11.CylinderMetric





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

theorem cylinderMetricForm_apply {n : ℕ} {X : Type*} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
    {D : SmoothSpacetimeInterval K} {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder F D C) (t : D.Point) (x : C)
    (v w : EuclideanSpace ℝ (Fin n)) :
    cylinderMetricForm e t x v w = F.horizontalMetric.inner (e.toSpacetime (t, x))
      (cylinderSpatialEquiv e t x v) (cylinderSpatialEquiv e t x w) := rfl

end PoincareConjecture.Proofs.M11
