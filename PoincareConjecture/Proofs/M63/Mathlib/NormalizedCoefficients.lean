import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv










set_option autoImplicit false



theorem HasDerivAt.div_sqrt_sq_mul_sq_add_sq {f : ℝ → ℝ} {f' x A B : ℝ}
    (hf : HasDerivAt f f' x) (hB : B ≠ 0) :
    HasDerivAt (fun s => f s / Real.sqrt (A ^ 2 * f s ^ 2 + B ^ 2))
      (B ^ 2 * f' / Real.sqrt (A ^ 2 * f x ^ 2 + B ^ 2) ^ 3) x := by
  have hD : 0 < A ^ 2 * f x ^ 2 + B ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (f x)))
      (sq_pos_of_ne_zero hB)
  have hr := Real.sqrt_pos.mpr hD
  have hs := Real.sq_sqrt hD.le
  have hroot : HasDerivAt (fun s => Real.sqrt (A ^ 2 * f s ^ 2 + B ^ 2))
      (A ^ 2 * f x * f' / Real.sqrt (A ^ 2 * f x ^ 2 + B ^ 2)) x := by
    convert HasDerivAt.sqrt (((hf.pow 2).const_mul (A ^ 2)).add_const (B ^ 2))
      hD.ne' using 1
    · ext s
      simp only [Pi.pow_apply]
    · simp only [Pi.pow_apply]
      field_simp
      ring
  apply (hf.div hroot hr.ne').congr_deriv
  field_simp
  rw [hs]
  ring



theorem HasDerivAt.const_div_sqrt_sq_mul_sq_add_sq {f : ℝ → ℝ} {f' x A B : ℝ}
    (hf : HasDerivAt f f' x) (hB : B ≠ 0) :
    HasDerivAt (fun s => B / Real.sqrt (A ^ 2 * f s ^ 2 + B ^ 2))
      (-(A ^ 2 * B * f x * f') / Real.sqrt (A ^ 2 * f x ^ 2 + B ^ 2) ^ 3) x := by
  have hD : 0 < A ^ 2 * f x ^ 2 + B ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (f x)))
      (sq_pos_of_ne_zero hB)
  have hr := Real.sqrt_pos.mpr hD
  have hroot : HasDerivAt (fun s => Real.sqrt (A ^ 2 * f s ^ 2 + B ^ 2))
      (A ^ 2 * f x * f' / Real.sqrt (A ^ 2 * f x ^ 2 + B ^ 2)) x := by
    convert HasDerivAt.sqrt (((hf.pow 2).const_mul (A ^ 2)).add_const (B ^ 2))
      hD.ne' using 1
    · ext s
      simp only [Pi.pow_apply]
    · simp only [Pi.pow_apply]
      field_simp
      ring
  apply ((hasDerivAt_const x B).div hroot hr.ne').congr_deriv
  field_simp
  ring
