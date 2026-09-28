import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts









set_option autoImplicit false

open Set
open scoped intervalIntegral

namespace Real



theorem hasDerivAt_affine_smoothTransition (s t y : ℝ) :
    HasDerivAt (fun r => s + (t - s) * smoothTransition r)
      ((t - s) * deriv smoothTransition y) y :=
  (((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero y).hasDerivAt.const_mul
    (t - s)).const_add s



theorem affine_smoothTransition_deriv_nonneg {s t : ℝ} (hst : s ≤ t) (y : ℝ) :
    0 ≤ (t - s) * deriv smoothTransition y :=
  mul_nonneg (sub_nonneg.mpr hst) smoothTransition.monotone.deriv_nonneg



theorem integral_affine_smoothTransition {s t : ℝ} (hst : s ≤ t)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc s t)) :
    (∫ y in (0 : ℝ)..1, ((t - s) * deriv smoothTransition y) *
      f (s + (t - s) * smoothTransition y)) = ∫ r in s..t, f r := by
  have hcont : Continuous (fun y => (t - s) * deriv smoothTransition y) :=
    continuous_const.mul ((smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num))
  have h := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := 1)
    (fun y _ => hasDerivAt_affine_smoothTransition s t y) hcont.continuousOn
    (hf.mono (by
      rintro _ ⟨y, _, rfl⟩
      have h0 := mul_nonneg (sub_nonneg.mpr hst) (smoothTransition.nonneg y)
      have h1 := mul_le_mul_of_nonneg_left (smoothTransition.le_one y) (sub_nonneg.mpr hst)
      constructor <;> linarith))
  simpa only [Function.comp_apply, smul_eq_mul, smoothTransition.zero, smoothTransition.one,
    mul_zero, add_zero, mul_one, add_sub_cancel] using h

end Real
