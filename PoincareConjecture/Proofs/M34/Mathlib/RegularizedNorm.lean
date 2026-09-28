import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open scoped ContDiff

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def regularizedNorm (e : ℝ) (x : E) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + e ^ 2)

theorem regularizedNorm_pos {e : ℝ} (he : 0 < e) (x : E) :
    0 < regularizedNorm e x := by
  unfold regularizedNorm
  positivity

theorem norm_le_regularizedNorm (e : ℝ) (x : E) :
    ‖x‖ ≤ regularizedNorm e x := by
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ regularizedNorm e x := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg e))

theorem regularizedNorm_zero {e : ℝ} (he : 0 ≤ e) :
    regularizedNorm e (0 : E) = e := by
  simp only [regularizedNorm, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    Real.sqrt_sq he]

variable [InnerProductSpace ℝ E]

theorem regularizedNorm_contDiff {e : ℝ} (he : 0 < e) :
    ContDiff ℝ ∞ (regularizedNorm e : E → ℝ) := by
  exact ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun _ => by positivity)

theorem regularizedNorm_hasFDerivAt {e : ℝ} (he : 0 < e) (x : E) :
    HasFDerivAt (regularizedNorm e)
      ((regularizedNorm e x)⁻¹ • innerSL ℝ x) x := by
  have hpos : 0 < ‖x‖ ^ 2 + e ^ 2 := by positivity
  convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (e ^ 2)).sqrt
    hpos.ne' using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, regularizedNorm, two_smul]
  change (Real.sqrt (‖x‖ ^ 2 + e ^ 2))⁻¹ * inner ℝ x v =
    1 / (2 * Real.sqrt (‖x‖ ^ 2 + e ^ 2)) * (inner ℝ x v + inner ℝ x v)
  field_simp
  ring

end Poincare
