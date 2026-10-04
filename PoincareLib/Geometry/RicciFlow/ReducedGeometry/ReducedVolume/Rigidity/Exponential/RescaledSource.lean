import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiating the Euclidean source rescaling

At positive backward time the source point y/(2 sqrt(t)) has velocity
minus its radial vector divided by 2t. This cancels the radial exponential
velocity in Morgan-Tian Proposition 7.27.
-/

set_option autoImplicit false

namespace PoincareMT.ReducedVolume

/-- The derivative of the inverse Euclidean spatial scale at positive time. -/
theorem inverse_double_sqrt_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹)
      (-(2 * t)⁻¹ * (2 * Real.sqrt t)⁻¹) t := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  apply (((Real.hasDerivAt_sqrt ht.ne').const_mul 2).inv
    (mul_ne_zero (by norm_num) hs)).congr_deriv
  field_simp [ht.ne', hs]
  nlinarith [Real.sq_sqrt ht.le]

/-- A fixed Euclidean point under the inverse scale has exactly negative radial velocity. -/
theorem inverse_double_sqrt_smul_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ (2 * Real.sqrt s)⁻¹ • y)
      (-(2 * t)⁻¹ • ((2 * Real.sqrt t)⁻¹ • y)) t := by
  simpa only [mul_smul] using (inverse_double_sqrt_hasDerivAt ht).smul_const y

end PoincareMT.ReducedVolume
