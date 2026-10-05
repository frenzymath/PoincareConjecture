import PoincareLib.Geometry.RicciFlow.Harnack.Basic

/-!
# Completeness of a compact Riemannian manifold

The actual Riemannian emetric has the original manifold topology, so
compactness gives the frozen metric-completeness predicate. This is the
completeness of compact doubles in Morgan-Tian Theorem 12.5, p. 297.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

/-- A compact Riemannian manifold is complete for its actual metric
(Theorem 12.5, p. 297, compact-double derivation). -/
theorem metricComplete_of_compact {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [CompactSpace M] (g : RiemannianMetric n M) : MetricComplete g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change CompleteSpace M
  infer_instance

end PoincareMT.RiemannianMetric
