import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/Calibration.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Euclidean normalization of the selected Hausdorff measure

Haar uniqueness identifies the unit-ball calibration in M10 with Lebesgue
measure for the actual Euclidean L2 norm. No numerical value of uncalibrated
Hausdorff measure is presumed, and dimension zero is included.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PoincareMT.SurgeryVolume.Measure

/-- Top-dimensional Hausdorff measure on the model space is an additive Haar measure. -/
theorem euclideanHausdorff_isAddHaarMeasure (n : ℕ) :
    Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa using (inferInstance : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) :
      Measure (EuclideanSpace ℝ (Fin n))))

/-- The denominator in M10's calibration is positive. -/
theorem euclideanHausdorff_unitBall_pos (n : ℕ) :
    0 < Measure.hausdorffMeasure (n : ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let := euclideanHausdorff_isAddHaarMeasure n
  exact Metric.measure_ball_pos _ _ zero_lt_one

/-- The denominator in M10's calibration is finite. -/
theorem euclideanHausdorff_unitBall_lt_top (n : ℕ) :
    Measure.hausdorffMeasure (n : ℝ)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ∞ := by
  let := euclideanHausdorff_isAddHaarMeasure n
  exact measure_ball_lt_top

/-- The actual unit-ball calibration is strictly positive. -/
theorem euclideanVolumeCalibration_pos (n : ℕ) : 0 < euclideanVolumeCalibration n :=
  ENNReal.div_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne'
    (euclideanHausdorff_unitBall_lt_top n).ne

/-- The actual unit-ball calibration is finite. -/
theorem euclideanVolumeCalibration_lt_top (n : ℕ) : euclideanVolumeCalibration n < ∞ :=
  ENNReal.div_lt_top measure_ball_lt_top.ne (euclideanHausdorff_unitBall_pos n).ne'

/-- M10's calibrated Euclidean Hausdorff measure is Lebesgue measure. -/
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

end PoincareMT.SurgeryVolume.Measure
