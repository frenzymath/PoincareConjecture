import PoincareConjecture.Definitions.Ch04.Harnack









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric



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

end PoincareConjecture.RiemannianMetric
