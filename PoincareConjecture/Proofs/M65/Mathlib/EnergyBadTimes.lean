import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real









set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral

namespace PoincareConjecture.M65




theorem energy_badTimes_measure_le {energy : ℝ → ℝ} {a b C B : ℝ}
    (hab : a ≤ b) (hnonneg : ∀ t, 0 ≤ energy t)
    (hintegrable : IntervalIntegrable energy volume a b)
    (hbound : (∫ t in a..b, energy t) ≤ C) (hB : 0 < B) :
    volume.real {t | t ∈ Icc a b ∧ B < energy t} ≤ C / B := by
  have hint : Integrable energy (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hintegrable
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)] energy)
    hint B
  rw [measureReal_restrict_apply' measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hmarkov
  have hweak : volume.real ({t | B ≤ energy t} ∩ Icc a b) ≤ C / B := by
    apply (le_div_iff₀ hB).mpr
    simpa only [mul_comm] using hmarkov.trans hbound
  apply le_trans (measureReal_mono ?_ ?_) hweak
  · intro t ht
    exact ⟨ht.2.le, ht.1⟩
  · apply ne_top_of_le_ne_top _ (measure_mono inter_subset_right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

end PoincareConjecture.M65
