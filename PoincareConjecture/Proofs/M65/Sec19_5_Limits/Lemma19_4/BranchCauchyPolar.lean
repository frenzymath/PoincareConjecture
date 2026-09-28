import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyOperator
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Metric Complex
open scoped Topology ContDiff ComplexConjugate

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]



def dbarLinear : (ℂ →L[ℝ] E) →L[ℝ] E :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ E 1 +
    I • ContinuousLinearMap.apply ℝ E I)



def dbar (ψ : ℂ → E) (z : ℂ) : E := dbarLinear (fderiv ℝ ψ z)



theorem continuous_dbar {ψ : ℂ → E} (hψ : ContDiff ℝ 1 ψ) : Continuous (dbar ψ) :=
  dbarLinear.continuous.comp (hψ.continuous_fderiv one_ne_zero)



theorem realLinear_apply_complex (D : ℂ →L[ℝ] E) (z : ℂ) :
    D z = (z.re : ℂ) • D 1 + (z.im : ℂ) • D I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    simp only [real_smul, mul_one, re_add_im]
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]




theorem realLinear_polar_dbar (D : ℂ →L[ℝ] E) {e : ℂ} (he : ‖e‖ = 1) :
    e⁻¹ • (D 1 + I • D I) = D e + I • D (I * e) := by
  have hconj : conj e = (e.re : ℂ) - (e.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [Complex.inv_eq_conj he, hconj, realLinear_apply_complex D e,
    realLinear_apply_complex D (I * e)]
  simp only [I_mul_re, I_mul_im, ofReal_neg]
  simp only [smul_add, smul_smul, sub_mul, mul_assoc, I_mul_I, mul_neg_one, sub_neg_eq_add]
  module




theorem radial_cauchy_dbar (D : ℂ →L[ℝ] E) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r • ((circleMap 0 r θ)⁻¹ • dbarLinear D) =
      (2 : ℂ)⁻¹ • (D (circleMap 0 1 θ) + I • D (I * circleMap 0 1 θ)) := by
  have he : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hc : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by simp [circleMap]
  rw [hc, mul_inv, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  have hscalar : (r : ℂ) * ((r : ℂ)⁻¹ * (circleMap 0 1 θ)⁻¹) =
      (circleMap 0 1 θ)⁻¹ := by
    rw [← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr hr.ne'), one_mul]
  rw [hscalar]
  simp only [dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply]
  rw [smul_comm, realLinear_polar_dbar D he]

end PoincareConjecture.M65Branch
