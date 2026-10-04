import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A smooth approximation to the norm

The function `sqrt (norm x ^ 2 + e ^ 2)` avoids differentiating the norm
at zero. It is used for the radial distance argument in Morgan-Tian
Lemma 12.2, printed pp. 294-295; see the M34 radial-distance derivation.
The statements hold on every real inner product space.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E]

/-- Smooth positive regularization of the norm used in the distance
argument for Morgan-Tian Lemma 12.2, pp. 294-295. -/
noncomputable def regularizedNorm (e : ℝ) (x : E) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + e ^ 2)

/-- A positive regularization parameter makes the square root strictly
positive everywhere (Lemma 12.2 distance argument, pp. 294-295). -/
theorem regularizedNorm_pos {e : ℝ} (he : 0 < e) (x : E) :
    0 < regularizedNorm e x := by
  unfold regularizedNorm
  positivity

/-- The regularized norm bounds the ordinary norm from above
(Lemma 12.2 distance argument, pp. 294-295). -/
theorem norm_le_regularizedNorm (e : ℝ) (x : E) :
    ‖x‖ ≤ regularizedNorm e x := by
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ regularizedNorm e x := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg e))

/-- The error at the origin is exactly the positive regularization
parameter (Lemma 12.2 distance argument, pp. 294-295). -/
theorem regularizedNorm_zero {e : ℝ} (he : 0 ≤ e) :
    regularizedNorm e (0 : E) = e := by
  simp only [regularizedNorm, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    Real.sqrt_sq he]

variable [InnerProductSpace ℝ E]

/-- Smoothness holds at the origin as well as away from it
(Lemma 12.2 distance argument, pp. 294-295). -/
theorem regularizedNorm_contDiff {e : ℝ} (he : 0 < e) :
    ContDiff ℝ ∞ (regularizedNorm e : E → ℝ) := by
  exact ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun _ => by positivity)

/-- The differential of the regularized norm has a nonzero denominator
at every point (Lemma 12.2 distance argument, pp. 294-295). -/
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
