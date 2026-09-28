import Mathlib.MeasureTheory.Integral.Lebesgue.Countable









set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal

namespace ENNReal



theorem tsum_liminf_le {ι κ : Type*} {l : Filter ι} [IsCountablyGenerated l]
    (f : ι → κ → ℝ≥0∞) :
    (∑' k, liminf (fun t => f t k) l) ≤ liminf (fun t => ∑' k, f t k) l := by
  let : MeasurableSpace κ := ⊤
  simpa only [lintegral_count] using
    (lintegral_liminf_le (μ := Measure.count) (f := f) (u := l)
      (fun _ => measurable_from_top))

end ENNReal
