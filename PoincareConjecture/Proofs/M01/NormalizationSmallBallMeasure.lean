import PoincareConjecture.Proofs.M01.NormalizationEuclideanVolume

set_option autoImplicit false

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace PoincareConjecture

variable {M F : Type*} [EMetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]

theorem m01_hausdorff_coordinateBall_le [NormedSpace ℝ F] (e : OpenPartialHomeomorph M F)
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

end PoincareConjecture
