import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Transport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

theorem cylinderMetric_inner_eq {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I} {T : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    {e : CompatibleSpacetimeCylinder S T C} (g h : SpacetimeCylinderMetric e)
    (t : T.Point) (x : C) (v w : TangentSpace (𝓡 n) x) :
    (g.metric t.val).inner x v w = (h.metric t.val).inner x v w := by
  have ht : g.spatialTangentEquiv t x = h.spatialTangentEquiv t x := by
    apply ContinuousLinearEquiv.ext
    funext z
    apply Subtype.ext
    rw [g.spatialTangentEquiv_eq, h.spatialTangentEquiv_eq]
  rw [g.metric_eq, h.metric_eq, ht]

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem domain_cylinder_metric
    (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C)
    (g : SpacetimeCylinderMetric e)
    (h : SpacetimeCylinderMetric ((domainTransport R Q hQ a).cylinderEquiv C K e))
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point)
    (x : C) (v w : TangentSpace (𝓡 n) x) :
    (h.metric s.val).inner x v w =
      Q * (g.metric (parabolicTimeInv Q a s.val)).inner x v w := by
  exact cylinderMetric_inner_eq h
    (transportedCylinderMetric (R := R) (Q := Q) (hQ := hQ) (a := a) K e g) s x v w

theorem domain_cylinder_metric_exists
    (H : CompatibleSpacetimeTheory.{u, v} R.spacetime R.timeIntervals)
    (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval K) C) :
    Nonempty (SpacetimeCylinderMetric ((domainTransport R Q hQ a).cylinderEquiv C K e)) := by
  obtain ⟨g⟩ := H.cylinder_metric C K e
  exact ⟨transportedCylinderMetric K e g⟩

end PoincareConjecture.ParabolicRescaling
