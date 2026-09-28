import PoincareConjecture.Proofs.M47.TerminalCommonIntervalLimitIdentities
import Mathlib.Topology.Instances.ENNReal.Lemmas









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal

namespace PoincareConjecture.M47

theorem terminalCommonInterval_distance_eq_of_all_factors
    {d e : ℝ≥0∞}
    (hlow : ∀ r : ℝ, 0 < r → r < 1 → ENNReal.ofReal r * d ≤ e)
    (hupp : ∀ r : ℝ, 0 < r → r < 1 → e ≤ ENNReal.ofReal r⁻¹ * d) :
    e = d := by
  have hde : d ≤ e := by
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    by_cases hzero : a = 0
    · simp [hzero]
    · have htop : a ≠ ∞ := ne_top_of_lt (lt_trans ha
        (by norm_num : (1 : ℝ≥0∞) < ∞))
      have ha0 : 0 < a.toReal := ENNReal.toReal_pos hzero htop
      have ha1 : a.toReal < 1 := by
        simpa using (ENNReal.toReal_lt_toReal htop (by norm_num :
          (1 : ℝ≥0∞) ≠ ∞)).2 ha
      have hh := hlow a.toReal ha0 ha1
      rw [ENNReal.ofReal_toReal htop] at hh
      exact hh
  have hed : e ≤ d := by
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    by_cases hzero : a = 0
    · simp [hzero]
    · have htop : a ≠ ∞ := ne_top_of_lt (lt_trans ha
        (by norm_num : (1 : ℝ≥0∞) < ∞))
      have ha0 : 0 < a.toReal := ENNReal.toReal_pos hzero htop
      have ha1 : a.toReal < 1 := by
        simpa using (ENNReal.toReal_lt_toReal htop (by norm_num :
          (1 : ℝ≥0∞) ≠ ∞)).2 ha
      have hb := hupp a.toReal ha0 ha1
      have hcancel : ENNReal.ofReal a.toReal * ENNReal.ofReal a.toReal⁻¹ = 1 := by
        rw [← ENNReal.ofReal_mul ha0.le, mul_inv_cancel₀ (ne_of_gt ha0),
          ENNReal.ofReal_one]
      calc
        a * e = ENNReal.ofReal a.toReal * e := by rw [ENNReal.ofReal_toReal htop]
        _ ≤ ENNReal.ofReal a.toReal * (ENNReal.ofReal a.toReal⁻¹ * d) :=
          mul_le_mul_right hb _
        _ = d := by rw [← mul_assoc, hcancel, one_mul]
  exact le_antisymm hed hde

end PoincareConjecture.M47
