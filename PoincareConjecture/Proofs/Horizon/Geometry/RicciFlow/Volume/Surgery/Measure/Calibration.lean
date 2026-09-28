import PoincareConjecture.Proofs.M10.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique




















set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.SurgeryVolume.Measure


theorem euclideanHausdorff_isAddHaarMeasure (n : ℕ) :
    Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa using (inferInstance : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) :
      Measure (EuclideanSpace ℝ (Fin n))))


theorem euclideanHausdorff_unitBall_pos (n : ℕ) :
    0 < Measure.hausdorffMeasure (n : ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let := euclideanHausdorff_isAddHaarMeasure n
  exact Metric.measure_ball_pos _ _ zero_lt_one


theorem euclideanHausdorff_unitBall_lt_top (n : ℕ) :
    Measure.hausdorffMeasure (n : ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ∞ := by
  let := euclideanHausdorff_isAddHaarMeasure n
  exact measure_ball_lt_top


theorem euclideanVolumeCalibration_pos (n : ℕ) : 0 < euclideanVolumeCalibration n :=
  ENNReal.div_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne'
    (euclideanHausdorff_unitBall_lt_top n).ne


theorem euclideanVolumeCalibration_lt_top (n : ℕ) : euclideanVolumeCalibration n < ∞ :=
  ENNReal.div_lt_top measure_ball_lt_top.ne (euclideanHausdorff_unitBall_pos n).ne'


theorem euclideanVolumeCalibration_smul_hausdorff (n : ℕ) :
    euclideanVolumeCalibration n •
      (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
  let H : Measure (EuclideanSpace ℝ (Fin n)) := Measure.hausdorffMeasure (n : ℝ)
  let : Measure.IsAddHaarMeasure H := euclideanHausdorff_isAddHaarMeasure n
  let c : NNReal := Measure.addHaarScalarFactor volume H
  have hhaar : (volume : Measure (EuclideanSpace ℝ (Fin n))) = c • H :=
    Measure.isAddLeftInvariant_eq_smul volume H
  have hball := congrArg
    (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦ μ (Metric.ball 0 1)) hhaar
  have hc : euclideanVolumeCalibration n = (c : ℝ≥0∞) := by
    unfold euclideanVolumeCalibration
    rw [hball]
    exact ENNReal.mul_div_cancel_right (euclideanHausdorff_unitBall_pos n).ne'
      (euclideanHausdorff_unitBall_lt_top n).ne
  rw [hc]
  exact hhaar.symm

end PoincareConjecture.SurgeryVolume.Measure
