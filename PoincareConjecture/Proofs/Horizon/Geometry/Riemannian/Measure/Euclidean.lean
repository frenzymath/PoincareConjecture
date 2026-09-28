import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

private theorem euclideanHausdorffMeasure_congr {X : Type*} [MeasurableSpace X]
    (m m' : EMetricSpace X)
    (hb : @BorelSpace X m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      inferInstance)
    (hb' : @BorelSpace X m'.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      inferInstance)
    (h : m = m') (n : ℕ) :
    @Measure.euclideanHausdorffMeasure X m inferInstance hb n =
      @Measure.euclideanHausdorffMeasure X m' inferInstance hb' n := by
  subst m'
  rfl

@[simp] theorem euclideanMetric_volumeMeasure (n : ℕ) :
    (euclideanMetric n).volumeMeasure =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let m₀ : EMetricSpace E := inferInstance
  let g := euclideanMetric n
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace (𝓡 n) : E → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  have hm : EMetricSpace.ofRiemannianMetric (𝓡 n) E = m₀ := by
    apply EMetricSpace.ext
    ext x y
    exact euclideanMetric_edist x y
  exact (euclideanHausdorffMeasure_congr _ _ inferInstance inferInstance hm n).trans
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n)

end PoincareConjecture.RiemannianMetric
