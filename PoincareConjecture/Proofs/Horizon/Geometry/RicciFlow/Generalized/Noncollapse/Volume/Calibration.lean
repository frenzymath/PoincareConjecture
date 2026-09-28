import PoincareConjecture.Proofs.M15.Thm1_34_Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Generalized.Noncollapse

theorem euclideanVolumeCalibration_eq_addHaarScalarFactor (n : ℕ) :
    euclideanVolumeCalibration n =
      (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) : ℝ≥0∞) := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := Measure.hausdorffMeasure (n : ℝ)
  have hμpos : 0 < μ (Metric.ball 0 1) :=
    Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr zero_lt_one)
  have hμfinite : μ (Metric.ball 0 1) ≠ ⊤ :=
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).measure_lt_top).ne
  have hvalue : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1) =
      (Measure.addHaarScalarFactor volume μ : ℝ≥0∞) * μ (Metric.ball 0 1) := by
    simpa only [ENNReal.smul_def, smul_eq_mul] using
      Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen
        (volume : Measure (EuclideanSpace ℝ (Fin n))) μ
        (s := Metric.ball 0 1) Metric.isOpen_ball
  change (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1) /
    μ (Metric.ball 0 1) = _
  rw [hvalue, div_eq_mul_inv, ENNReal.mul_inv_cancel_right hμpos.ne' hμfinite]

theorem calibratedMetricVolume_eq_euclideanHausdorff
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] (g : RiemannianMetric n M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    calibratedMetricVolume g = Measure.euclideanHausdorffMeasure n := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change calibratedMetricVolume g = Measure.euclideanHausdorffMeasure n
  rw [Measure.euclideanHausdorffMeasure_def, ENNReal.smul_def,
    ← euclideanVolumeCalibration_eq_addHaarScalarFactor]
  rfl

end PoincareConjecture.Generalized.Noncollapse
