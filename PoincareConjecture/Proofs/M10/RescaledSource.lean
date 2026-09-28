import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false

namespace PoincareConjecture.M10


theorem inverse_double_sqrt_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹)
      (-(2 * t)⁻¹ * (2 * Real.sqrt t)⁻¹) t := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  apply (((Real.hasDerivAt_sqrt ht.ne').const_mul 2).inv
    (mul_ne_zero (by norm_num) hs)).congr_deriv
  field_simp [ht.ne', hs]
  nlinarith [Real.sq_sqrt ht.le]


theorem inverse_double_sqrt_smul_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹ • y)
      (-(2 * t)⁻¹ • ((2 * Real.sqrt t)⁻¹ • y)) t := by
  simpa only [mul_smul] using (inverse_double_sqrt_hasDerivAt ht).smul_const y

end PoincareConjecture.M10
