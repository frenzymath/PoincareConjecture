import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformPolar
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

noncomputable def cauchyRiemannDerivative (f : ℂ → V) (z : ℂ) : V :=
  (1 / 2 : ℝ) • (fderiv ℝ f z 1 + I • fderiv ℝ f z I)

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in
private theorem realLinear_apply (L : ℂ →L[ℝ] V) (c : ℂ) :
    L c = c.re • L 1 + c.im • L I := by
  conv_lhs => rw [← re_add_im c]
  rw [map_add, show (c.re : ℂ) = c.re • (1 : ℂ) by simp [real_smul],
    show (c.im : ℂ) * I = c.im • I by rfl, map_smul, map_smul]

private theorem realLinear_polar (L : ℂ →L[ℝ] V) (θ : ℝ) :
    (circleMap 0 1 θ)⁻¹ • (L 1 + I • L I) =
      L (circleMap 0 1 θ) + I • L (I * circleMap 0 1 θ) := by
  have hc : (circleMap 0 1 θ)⁻¹ =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    apply Complex.ext <;>
      simp [circleMap_zero_inv, circleMap_zero_re, circleMap_zero_im,
        Real.cos_neg, Real.sin_neg, cos_ofReal_re, sin_ofReal_re]
  rw [hc, realLinear_apply L (circleMap 0 1 θ),
    realLinear_apply L (I * circleMap 0 1 θ)]
  simp only [circleMap_zero_re, circleMap_zero_im, one_mul, mul_re, I_re,
    zero_mul, mul_im, I_im, zero_sub, zero_add]
  have hscalar (a b : ℝ) :
      ((a : ℂ) - (b : ℂ) * I) • (L 1 + I • L I) =
        a • L 1 + b • L I + I • (-b • L 1 + a • L I) := by
    have hs (t : ℝ) (v : V) : (t : ℂ) • v = t • v :=
      algebraMap_smul ℂ t v
    simp only [smul_add, sub_smul, mul_smul, hs, neg_smul, smul_neg]
    rw [← mul_smul I I, I_mul_I, neg_one_smul]
    simp only [smul_neg, sub_neg_eq_add, smul_comm I a, smul_comm I b]
    abel
  exact hscalar _ _

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem hasDerivAt_polar_radius {f : ℂ → V} (hf : Differentiable ℝ f)
    (z : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => f (z - circleMap 0 s θ))
      (-(fderiv ℝ f (z - circleMap 0 r θ) (circleMap 0 1 θ))) r := by
  have hi : HasDerivAt (fun s : ℝ => z - circleMap 0 s θ)
      (-circleMap 0 1 θ) r := by
    simpa only [circleMap_zero, ofReal_one, one_mul, zero_sub,
      ofRealCLM_apply, Pi.sub_def] using
      ((hasDerivAt_const r z).sub (Complex.ofRealCLM.hasDerivAt.mul_const
        (cexp (θ * I))))
  simpa only [Function.comp_def, map_neg] using
    (hf (z - circleMap 0 r θ)).hasFDerivAt.comp_hasDerivAt r hi

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem hasDerivAt_polar_angle {f : ℂ → V} (hf : Differentiable ℝ f)
    (z : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => f (z - circleMap 0 r t))
      (-r • (fderiv ℝ f (z - circleMap 0 r θ) (I * circleMap 0 1 θ))) θ := by
  have h := (hf (z - circleMap 0 r θ)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ z).sub (hasDerivAt_circleMap 0 r θ))
  have he : (0 : ℂ) - circleMap 0 r θ * I =
      (-r) • (I * circleMap 0 1 θ) := by
    simp only [circleMap_zero, ofReal_one, one_mul, real_smul, ofReal_neg]
    ring
  simpa only [he, map_smul, Function.comp_def, Pi.sub_apply] using h

theorem cauchyRiemannDerivative_polar {f : ℂ → V} (hf : Differentiable ℝ f)
    (z : ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    (circleMap 0 1 θ)⁻¹ • cauchyRiemannDerivative f (z - circleMap 0 r θ) =
      -(1 / 2 : ℝ) • deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r -
      (1 / (2 * r) : ℝ) • (I • deriv (fun t : ℝ => f (z - circleMap 0 r t)) θ) := by
  rw [(hasDerivAt_polar_radius hf z r θ).deriv,
    (hasDerivAt_polar_angle hf z r θ).deriv, cauchyRiemannDerivative,
    smul_comm (circleMap 0 1 θ)⁻¹ (1 / 2 : ℝ), realLinear_polar]
  simp only [smul_add, neg_smul, smul_neg, neg_neg, sub_neg_eq_add]
  rw [smul_comm I r, smul_smul,
    show (1 / (2 * r)) * r = (1 / 2 : ℝ) by field_simp]

end PoincareConjecture.M60
