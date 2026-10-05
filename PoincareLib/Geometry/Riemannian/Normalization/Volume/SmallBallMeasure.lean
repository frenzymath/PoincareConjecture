import PoincareLib.Geometry.Riemannian.Normalization.Volume.Euclidean

/-!
# Small-ball measure from an almost isometric chart

The forward chart estimate can be applied to a metric ball once that ball is
known to lie in the inverse image of a coordinate neighborhood. Monotonicity
then compares the coordinate ball with the chart image. This isolates the
measure-theoretic part of the local noncollapsing argument.
-/

set_option autoImplicit false

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace PoincareMT

variable {M F : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]

theorem normalization_hausdorff_coordinateBall_le [NormedSpace ℝ F] (e : OpenPartialHomeomorph M F)
    (C : ℝ≥0) (S : Set M) (z : F) (r : ℝ)
    (hLip : LipschitzOnWith C e S)
    (hball : Metric.ball z r ⊆ e '' S) :
    Measure.hausdorffMeasure (3 : ℝ) (Metric.ball z r) ≤
      (C : ℝ≥0∞) ^ 3 * Measure.hausdorffMeasure (3 : ℝ) S := by
  calc
    Measure.hausdorffMeasure (3 : ℝ) (Metric.ball z r) ≤
        Measure.hausdorffMeasure (3 : ℝ) (e '' S) :=
      measure_mono hball
    _ ≤ (C : ℝ≥0∞) ^ 3 * Measure.hausdorffMeasure (3 : ℝ) S := by
      simpa only [ENNReal.rpow_ofNat] using
        hLip.hausdorffMeasure_image_le (d := (3 : ℝ)) (by norm_num)

end PoincareMT
