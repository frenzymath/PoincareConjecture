import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem standardGaussianDensity_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hq : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert! (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1
    simp only [id_eq]
    ring
  have h := hq.exp.const_mul (1 / Real.sqrt (2 * Real.pi))
  have hfun : gaussianPDFReal 0 1 =
      fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-y ^ 2 / 2) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  rw [hfun]
  apply h.congr_deriv
  ring

theorem integrable_standardGaussian_density_smul {f : ℝ → F}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x • f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF] using h

theorem integral_standardGaussian_derivative {f f' : ℝ → F}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x • f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) = ∫ x, x • f x ∂gaussianReal 0 1 := by
  have hi := integrable_standardGaussian_density_smul hf
  have hi' := integrable_standardGaussian_density_smul hf'
  have hix := integrable_standardGaussian_density_smul hxf
  have hid : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) • f x) := by
    apply hix.neg.congr
    exact Eventually.of_forall (fun x => by
      simp only [Pi.neg_apply, smul_smul, neg_mul, neg_smul, mul_comm])
  have hparts := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ (E := F))
    (fun x _ => standardGaussianDensity_hasDerivAt x) (fun x _ => hderiv x) hi' hid hi
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  change (∫ x, gaussianPDFReal 0 1 x • f' x) =
    -(∫ x, (-x * gaussianPDFReal 0 1 x) • f x) at hparts
  rw [hparts, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [smul_smul, neg_mul, neg_smul, neg_neg, mul_comm])

end PoincareConjecture.M35.RadialGauge
