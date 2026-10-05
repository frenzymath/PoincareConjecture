import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/FatouSum.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Fatou's inequality for a family of nonnegative summands

The chart-cover volume argument for Morgan-Tian Lemma 17.12, p. 410,
uses Fatou first inside each chart and then across the chart family.
Counting measure gives the second inequality without finiteness premises.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal

namespace ENNReal

/-- Fatou for a family of summands, used to assemble chart volumes in
MT Lemma 17.12, p. 410; see the stage-6 regular-limit derivation. -/
theorem tsum_liminf_le {ι κ : Type*} {l : Filter ι} [IsCountablyGenerated l]
    (f : ι → κ → ℝ≥0∞) :
    (∑' k, liminf (fun t => f t k) l) ≤ liminf (fun t => ∑' k, f t k) l := by
  let : MeasurableSpace κ := ⊤
  simpa only [lintegral_count] using
    (lintegral_liminf_le (μ := Measure.count) (f := f) (u := l)
      (fun _ => measurable_from_top))

end ENNReal
