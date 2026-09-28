import PoincareConjecture.Definitions.Ch04.Harnack

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]

@[instance_reducible]
noncomputable def toEMetricSpace (g : RiemannianMetric n M) : EMetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) M

theorem toEMetricSpace_topology (g : RiemannianMetric n M) :
    g.toEMetricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

theorem toEMetricSpace_edist (g : RiemannianMetric n M) (x y : M) :
    g.toEMetricSpace.edist x y = g.edist x y := rfl

theorem metricComplete_iff_toEMetricSpace (g : RiemannianMetric n M) :
    MetricComplete g ↔ @CompleteSpace M g.toEMetricSpace.toUniformSpace := Iff.rfl

end PoincareConjecture.RiemannianMetric
