import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

theorem exists_continuous_convex_exhaustion
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    ∃ f : M → ℝ, Continuous f ∧ f p = 0 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x y, |f x - f y| ≤ (g.edist x y).toReal) ∧
      (∀ r : ℝ, IsCompact {x | f x ≤ r}) ∧
      ∀ (curve : ℝ → M) (a b : ℝ), g.IsGeodesicOn curve (Icc a b) →
        ConvexOn ℝ (Icc a b) (f ∘ curve) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  refine ⟨busemannExhaustion p, (lipschitz_busemannExhaustion p).continuous,
    busemannExhaustion_self p, busemannExhaustion_nonneg p, ?_, ?_, ?_⟩
  · intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
      (lipschitz_busemannExhaustion p).dist_le_mul x y
  · intro r
    by_cases hr : 0 ≤ r
    · have hset : {x | busemannExhaustion p x ≤ r} = horoballIntersection p r := by
        ext x
        exact busemannExhaustion_le_iff hr
      rw [hset]
      exact g.isCompact_horoballIntersection_of_nonnegativeSectional D hcomplete hsec hdist p hr
    · have hset : {x | busemannExhaustion p x ≤ r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hr ((busemannExhaustion_nonneg p x).trans hx)
      rw [hset]
      exact isCompact_empty
  · intro curve a b hcurve
    exact convexOn_busemannExhaustion_comp fun ray hray _ =>
      g.concaveOn_busemann_of_nonnegativeSectional D hcomplete hsec hdist hray hcurve

end PoincareConjecture.RiemannianMetric
