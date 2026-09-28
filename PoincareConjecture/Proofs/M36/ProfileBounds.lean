import PoincareConjecture.Statements.M36MetricSurgery
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring










set_option autoImplicit false

namespace PoincareConjecture.M36


theorem profile_term_le {q s : ℝ} (hq : 0 < q) (hs : 0 < s) :
    (q ^ 2 / s ^ 4) * Real.exp (-q / s) ≤ 24 / q ^ 2 := by
  have hexp := Real.pow_div_factorial_le_exp (q / s) (le_of_lt (div_pos hq hs)) 4
  norm_num at hexp
  have hinv := one_div_le_one_div_of_le
    (by positivity : 0 < (q / s) ^ 4 / 24) hexp
  calc
    (q ^ 2 / s ^ 4) * Real.exp (-q / s) =
        (q ^ 2 / s ^ 4) * (1 / Real.exp (q / s)) := by
      rw [neg_div, Real.exp_neg, one_div]
    _ ≤ (q ^ 2 / s ^ 4) * (1 / ((q / s) ^ 4 / 24)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 24 / q ^ 2 := by field_simp

theorem profile_term_lt {q s : ℝ} (hq : 100 < q) (hs : 0 < s) :
    (q ^ 2 / s ^ 4) * Real.exp (-q / s) < 1 / 100 := by
  have hq0 : 0 < q := by linarith
  refine (profile_term_le hq0 hs).trans_lt ?_
  apply (div_lt_iff₀ (sq_pos_of_pos hq0)).2
  nlinarith [sq_nonneg (q - 100)]


theorem largeQ_of_bounds (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants)
    (hq : 100 < K.q)
    (hA : 100 * (4 + g₀.cylindrical_end.radius) ^ 2 < K.q) :
    SurgeryProfileLargeQ g₀ K := by
  refine ⟨hA, ?_⟩
  intro s hs _
  exact profile_term_lt hq hs

theorem exists_profile_parameter (g₀ : StandardInitialMetric) :
    ∃ q : ℝ, 100 < q ∧ 100 * (4 + g₀.cylindrical_end.radius) ^ 2 < q := by
  refine ⟨101 + 100 * (4 + g₀.cylindrical_end.radius) ^ 2, ?_, ?_⟩
  · nlinarith [sq_nonneg (4 + g₀.cylindrical_end.radius)]
  · linarith


theorem exists_neck_threshold (g₀ : StandardInitialMetric) {upper : ℝ}
    (hupper : 0 < upper) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 200 ∧ delta ≤ upper ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
        4 + g₀.cylindrical_end.radius < epsilon⁻¹ := by
  let A := 4 + g₀.cylindrical_end.radius
  have hA : 0 < A + 1 := by
    dsimp [A]
    linarith [g₀.cylindrical_end.radius_pos]
  refine ⟨min upper (min (1 / 400) (1 / (A + 1))), ?_, ?_, ?_, ?_⟩
  · exact lt_min hupper (lt_min (by norm_num) (one_div_pos.mpr hA))
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · exact min_le_left _ _
  · intro epsilon hepsilon hle
    have hbound : epsilon ≤ 1 / (A + 1) :=
      hle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hinv := one_div_le_one_div_of_le hepsilon hbound
    simp only [one_div, inv_inv] at hinv
    change A < epsilon⁻¹
    linarith

end PoincareConjecture.M36
