import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts

set_option autoImplicit false

open Set

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

theorem coe_mem_shortArc_iff {d z : ℝ} (hd : 0 < d) (hdp : d < p)
    (hz : z ∈ Ioo 0 p) :
    (z : AddCircle p) ∈ ((↑) : ℝ → AddCircle p) '' Ioo (-d) d ↔
      z < d ∨ p - d < z := by
  have hzI : z ∈ Ico 0 (0 + p) := ⟨hz.1.le, by simpa only [zero_add] using hz.2⟩
  constructor
  · rintro ⟨t, ht, he⟩
    by_cases ht0 : 0 ≤ t
    · have htI : t ∈ Ico 0 (0 + p) := ⟨ht0, by linarith [ht.2]⟩
      have htz := (coe_eq_coe_iff_of_mem_Ico htI hzI).mp he
      exact Or.inl (htz ▸ ht.2)
    · have htpI : t + p ∈ Ico 0 (0 + p) := by
        constructor <;> linarith [ht.1]
      have hcoe : ((t + p : ℝ) : AddCircle p) = (t : AddCircle p) := by
        rw [coe_add, coe_period, add_zero]
      have htz := (coe_eq_coe_iff_of_mem_Ico htpI hzI).mp (hcoe.trans he)
      exact Or.inr (by linarith [ht.1])
  · rintro (hzlo | hzhi)
    · exact ⟨z, ⟨by linarith [hz.1], hzlo⟩, rfl⟩
    · refine ⟨z - p, ⟨by linarith, by linarith [hz.2]⟩, ?_⟩
      rw [coe_sub, coe_period, sub_zero]

theorem coe_center_mem_shortArc_iff {d s : ℝ} (hd : 0 < d) (hdhalf : d < p / 2)
    (hs : s ∈ Ioo (-p / 2) (p / 2)) :
    ((p / 2 + s : ℝ) : AddCircle p) ∈
      ((↑) : ℝ → AddCircle p) '' Ioo (-d) d ↔ p / 2 - d < |s| := by
  have hp : 0 < p := Fact.out
  rw [coe_mem_shortArc_iff p hd (by linarith) (by constructor <;> linarith [hs.1, hs.2])]
  constructor
  · rintro (h | h)
    · exact lt_of_lt_of_le (by linarith : p / 2 - d < -s) (neg_le_abs s)
    · exact lt_of_lt_of_le (by linarith : p / 2 - d < s) (le_abs_self s)
  · intro h
    by_cases hs0 : 0 ≤ s
    · rw [abs_of_nonneg hs0] at h
      exact Or.inr (by linarith)
    · rw [abs_of_neg (lt_of_not_ge hs0)] at h
      exact Or.inl (by linarith)

end AddCircle
