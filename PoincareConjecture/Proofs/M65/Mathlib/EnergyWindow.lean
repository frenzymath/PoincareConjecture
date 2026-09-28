import PoincareConjecture.Proofs.M65.Mathlib.EnergyBadTimes









set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral

namespace PoincareConjecture.M65



theorem exists_energy_le_in_window {energy : ℝ → ℝ} {a b s t C B : ℝ}
    (has : a ≤ s) (hst : s < t) (htb : t ≤ b)
    (hnonneg : ∀ r, 0 ≤ energy r)
    (hintegrable : IntervalIntegrable energy volume a b)
    (hbound : (∫ r in a..b, energy r) ≤ C) (hB : 0 < B)
    (hwindow : C / B < t - s) : ∃ r ∈ Ioo s t, energy r ≤ B := by
  by_contra hnone
  have hsubset : Ioo s t ⊆ {r | r ∈ Icc a b ∧ B < energy r} := by
    intro r hr
    refine ⟨⟨has.trans hr.1.le, hr.2.le.trans htb⟩, ?_⟩
    by_contra hbad
    exact hnone ⟨r, hr, le_of_not_gt hbad⟩
  have hfinite : volume {r | r ∈ Icc a b ∧ B < energy r} ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono fun _ hr => hr.1)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmeasure := (measureReal_mono hsubset hfinite).trans
    (energy_badTimes_measure_le (has.trans (hst.le.trans htb))
      hnonneg hintegrable hbound hB)
  rw [Real.volume_real_Ioo_of_le hst.le] at hmeasure
  exact (not_lt_of_ge hmeasure) hwindow

end PoincareConjecture.M65
