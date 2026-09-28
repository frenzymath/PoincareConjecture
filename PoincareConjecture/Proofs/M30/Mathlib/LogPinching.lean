import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith










set_option autoImplicit false

namespace PoincareConjecture.M30



theorem negative_le_scaled_of_log_pinching {R X Q B eta : ℝ}
    (hQ : 0 < Q) (hB : 0 ≤ B) (heta : 0 < eta)
    (hscale : Real.exp (B / eta + 4) ≤ eta * Q)
    (hR : R ≤ B * Q)
    (hpinch : 0 < X → 2 * X * (Real.log X - 3) ≤ R) :
    X ≤ eta * Q := by
  by_contra h
  have hX : eta * Q < X := lt_of_not_ge h
  have hXpos : 0 < X := (mul_pos heta hQ).trans hX
  have hlog : B / eta + 4 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hXpos).mpr
    exact hscale.trans hX.le
  have hdiv : B / eta * eta = B := div_mul_cancel₀ B heta.ne'
  have hdiv_nonneg : 0 ≤ B / eta := div_nonneg hB heta.le
  have hc : 0 < Real.log X - 3 := by linarith
  have heta_c : B < eta * (Real.log X - 3) := by
    have hmul := mul_le_mul_of_nonneg_left hlog heta.le
    nlinarith
  have hprod := mul_lt_mul_of_pos_right hX hc
  have hscale_prod := mul_lt_mul_of_pos_right heta_c hQ
  have hpositive : 0 < X * (Real.log X - 3) := mul_pos hXpos hc
  have hp := hpinch hXpos
  nlinarith

end PoincareConjecture.M30
