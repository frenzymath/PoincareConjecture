import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-!
# A uniform linear bound for nonnegative exponential increments

The scalar estimate used in Claim 19.23, Morgan--Tian pp. 453-454.
See M65 derivation 16.
-/

set_option autoImplicit false

namespace Real

/-- A bounded nonnegative exponential increment has a uniform linear
majorant; Claim 19.23, pp. 453-454, scalar estimate. -/
theorem exp_sub_one_le_mul_exp {x L : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) :
    exp x - 1 ≤ x * exp L := by
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_nonneg x)
  rw [← exp_add, add_neg_cancel, exp_zero] at h
  have hmono := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hL) hx
  nlinarith

end Real
