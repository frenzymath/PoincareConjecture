import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import PoincareConjecture.Proofs.M40.Mathlib.ConnectedEMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M40

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

@[instance_reducible]
noncomputable def metricSpaceOfRiemannianMetric (g : RiemannianMetric n M) :
    MetricSpace M := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

theorem metricSpaceOfRiemannianMetric_edist (g : RiemannianMetric n M) (x y : M) :
    @edist M (metricSpaceOfRiemannianMetric g).toEDist x y = g.edist x y := rfl

theorem metricSpaceOfRiemannianMetric_topology (g : RiemannianMetric n M) :
    (metricSpaceOfRiemannianMetric g).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M) := rfl

end PoincareConjecture.M40
