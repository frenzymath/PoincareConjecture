import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith








set_option autoImplicit false

namespace Real



theorem exp_sub_one_le_mul_exp {x L : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) :
    exp x - 1 ≤ x * exp L := by
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_nonneg x)
  rw [← exp_add, add_neg_cancel, exp_zero] at h
  have hmono := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hL) hx
  nlinarith

end Real
