import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem volumeMeasure_nullSingletonClass
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (g : RiemannianMetric n M) (hn : 0 < n) :
    NullSingletonClass g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change NullSingletonClass (Measure.euclideanHausdorffMeasure n : Measure M)
  let : NullSingletonClass (Measure.hausdorffMeasure (n : ℝ) : Measure M) :=
    Measure.nullSingletonClass_hausdorff M (Nat.cast_pos.mpr hn)
  refine ⟨fun x => ?_⟩
  simp only [Measure.euclideanHausdorffMeasure, Measure.smul_apply, measure_singleton,
    smul_zero]

end PoincareConjecture.RiemannianMetric
