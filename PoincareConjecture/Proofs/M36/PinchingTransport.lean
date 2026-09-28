import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace PoincareConjecture.M36

theorem pinching_log_bound_of_comparison {t R Rnew X Xnew : ℝ}
    (hRnew : 0 ≤ Rnew) (hR : R ≤ Rnew) (hXnew : 0 < Xnew) (hX : Xnew ≤ X)
    (hpinch : 0 < X → 2 * X * (Real.log X + Real.log (1 + t) - 3) ≤ R) :
    2 * Xnew * (Real.log Xnew + Real.log (1 + t) - 3) ≤ Rnew := by
  by_cases hfactor : Real.log Xnew + Real.log (1 + t) - 3 ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * Xnew) hfactor).trans hRnew
  · have hXpos : 0 < X := lt_of_lt_of_le hXnew hX
    have hlog : Real.log Xnew ≤ Real.log X := Real.log_le_log hXnew hX
    have hprod : 2 * Xnew * (Real.log Xnew + Real.log (1 + t) - 3) ≤
        2 * X * (Real.log X + Real.log (1 + t) - 3) :=
      mul_le_mul (by linarith) (by linarith) (le_of_lt (lt_of_not_ge hfactor))
        (by positivity)
    exact hprod.trans ((hpinch hXpos).trans hR)

theorem pinching_scalar_lower_bound_of_nonneg {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) :
    -6 / (1 + 4 * t) ≤ R :=
  (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-6 : ℝ) ≤ 0)
    (by linarith : 0 ≤ 1 + 4 * t)).trans hR

end PoincareConjecture.M36
