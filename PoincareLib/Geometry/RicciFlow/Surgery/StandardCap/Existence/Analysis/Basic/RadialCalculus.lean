import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiating radial coefficients

These elementary Cartesian formulas supply the connection computation for
Morgan-Tian Lemma 12.2, printed pp. 294-295. They apply to any real inner
product space and are used only away from the origin. See the M34
radial-curvature derivation for the metric and curvature conventions.
-/

set_option autoImplicit false

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The differential of radius away from the origin, for the Cartesian
calculation in Morgan-Tian Lemma 12.2, pp. 294-295. -/
theorem hasFDerivAt_radius {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert! h using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul]
  change ‖x‖⁻¹ * inner ℝ x v = 1 / (2 * ‖x‖) * (inner ℝ x v + inner ℝ x v)
  field_simp
  ring

/-- Chain rule for a scalar radial coefficient, retaining the radial
derivative rather than a totalized derivative at a singular point
(Lemma 12.2 connection calculation, pp. 294-295). -/
theorem hasFDerivAt_radial {f : ℝ → ℝ} {f' : ℝ} {x : E} (hx : x ≠ 0)
    (hf : HasDerivAt f f' ‖x‖) :
    HasFDerivAt (fun y : E => f ‖y‖) ((f' / ‖x‖) • innerSL ℝ x) x := by
  convert! hf.comp_hasFDerivAt x (hasFDerivAt_radius hx) using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- First derivative of a radial metric pairing in fixed Cartesian
directions (Lemma 12.2 connection calculation, pp. 294-295). -/
theorem fderiv_radial_pairing {c b : ℝ → ℝ} {c' b' : ℝ} {x : E}
    (hx : x ≠ 0) (hc : HasDerivAt c c' ‖x‖) (hb : HasDerivAt b b' ‖x‖)
    (u v w : E) :
    fderiv ℝ (fun y : E => c ‖y‖ * inner ℝ u v +
      b ‖y‖ * (inner ℝ y u * inner ℝ y v)) x w =
      c' / ‖x‖ * inner ℝ x w * inner ℝ u v +
      b' / ‖x‖ * inner ℝ x w * (inner ℝ x u * inner ℝ x v) +
      b ‖x‖ * (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v) := by
  have hu := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const u x)
  have hv := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const v x)
  have h := ((hasFDerivAt_radial hx hc).mul_const (inner ℝ u v)).add
    ((hasFDerivAt_radial hx hb).mul (hu.mul hv))
  change HasFDerivAt (fun y : E => c ‖y‖ * inner ℝ u v +
    b ‖y‖ * (inner ℝ y u * inner ℝ y v)) _ x at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    fderivInnerCLM_apply, inner_zero_right, zero_add, innerSL_apply_apply, smul_eq_mul,
    Pi.mul_apply, id_eq]
  ring

end Poincare
