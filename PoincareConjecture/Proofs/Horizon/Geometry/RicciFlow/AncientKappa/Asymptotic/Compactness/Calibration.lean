import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Calibrated
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure








set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem euclideanVolumeCalibration_eq_addHaarScalarFactor (n : ℕ) :
    euclideanVolumeCalibration n =
      (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) : ℝ≥0∞) := by
  rw [euclideanVolumeCalibration,
    Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen volume
      (Measure.hausdorffMeasure (n : ℝ)) Metric.isOpen_ball]
  change _ * _ / _ = _
  exact ENNReal.mul_div_cancel_right
    (Metric.measure_ball_pos (Measure.hausdorffMeasure (n : ℝ))
      (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_lt_top.ne

theorem calibratedMetricVolume_eq_volumeMeasure {n : ℕ} {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : calibratedMetricVolume g = g.volumeMeasure := by
  simp only [calibratedMetricVolume, RiemannianMetric.volumeMeasure,
    Measure.euclideanHausdorffMeasure, euclideanVolumeCalibration_eq_addHaarScalarFactor]
  rfl

theorem euclideanVolumeCalibration_pos (n : ℕ) : 0 < euclideanVolumeCalibration n := by
  exact ENNReal.div_pos (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_lt_top.ne

theorem euclideanVolumeCalibration_ne_top (n : ℕ) : euclideanVolumeCalibration n ≠ ⊤ := by
  exact ENNReal.div_ne_top measure_ball_lt_top.ne
    (Metric.measure_ball_pos (Measure.hausdorffMeasure (n : ℝ))
      (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (0 : ℝ) < 1)).ne'

theorem calibrated_noncollapse_to_hausdorff {n : ℕ} (C : FlowCarrier n) (g : C.metric)
    (E : Set C.carrier) {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hvol :
      letI := C.topologicalSpace
      letI := C.measurableSpace
      letI := C.borelSpace
      letI := C.chartedSpace
      letI := C.isManifold
      letI := C.t3Space
      ENNReal.ofReal (κ * r ^ n) ≤ calibratedMetricVolume g E) :
    ENNReal.ofReal ((κ / (euclideanVolumeCalibration n).toReal) * r ^ n) ≤
      C.metricHausdorffVolume g E := by
  have hc := euclideanVolumeCalibration_pos n
  have hct := euclideanVolumeCalibration_ne_top n
  have hcr : 0 < (euclideanVolumeCalibration n).toReal := ENNReal.toReal_pos hc.ne' hct
  change ENNReal.ofReal (κ * r ^ n) ≤
    euclideanVolumeCalibration n * C.metricHausdorffVolume g E at hvol
  have hscale : euclideanVolumeCalibration n *
      ENNReal.ofReal ((κ / (euclideanVolumeCalibration n).toReal) * r ^ n) =
      ENNReal.ofReal (κ * r ^ n) := by
    nth_rw 1 [← ENNReal.ofReal_toReal hct]
    rw [← ENNReal.ofReal_mul hcr.le]
    congr 1
    field_simp
  apply (ENNReal.mul_le_mul_iff_right hc.ne' hct).mp
  rwa [hscale]

end PoincareConjecture
