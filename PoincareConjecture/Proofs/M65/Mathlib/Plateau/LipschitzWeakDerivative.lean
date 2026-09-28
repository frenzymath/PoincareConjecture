import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic










set_option autoImplicit false

open MeasureTheory Measure Filter
open scoped SchwartzMap InnerProductSpace NNReal

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ] {C : ℝ≥0} {f : E → ℝ}





theorem inner_toLp_fderiv_schwartz (hf : LipschitzWith C f)
    (hsupport : HasCompactSupport f) (hfL2 : MemLp f 2 μ) (v : E)
    (hdL2 : MemLp (fun x => fderiv ℝ f x v) 2 μ) (test : 𝓢(E, ℝ)) :
    ⟪hdL2.toLp (fun x => fderiv ℝ f x v), test.toLp 2 μ⟫_ℝ =
      -(∫ x, hfL2.toLp f x * fderiv ℝ test x v ∂μ) := by
  let K : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 1 test, apply_nonneg _ _⟩
  have htest : LipschitzWith K test := by
    apply lipschitzWith_of_nnnorm_fderiv_le test.differentiable
    intro x
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ test x‖ ≤ SchwartzMap.seminorm ℝ 0 1 test
    simpa only [norm_iteratedFDeriv_one] using test.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  have hibp := htest.integral_lineDeriv_mul_eq (μ := μ) hf hsupport (-v)
  calc
    _ = ∫ x, fderiv ℝ f x v * test x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hdL2.coeFn_toLp, test.coeFn_toLp 2 μ] with x hx ht
      simp only [hx, ht, Real.inner_apply]
    _ = ∫ x, lineDeriv ℝ f x v * test x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
      rw [hx.lineDeriv_eq_fderiv]
    _ = ∫ x, lineDeriv ℝ test x (-v) * f x ∂μ := by
      simpa only [neg_neg] using hibp.symm
    _ = -(∫ x, hfL2.toLp f x * fderiv ℝ test x v ∂μ) := by
      simp_rw [test.differentiableAt.lineDeriv_eq_fderiv, map_neg, neg_mul, integral_neg]
      congr 1
      apply integral_congr_ae
      filter_upwards [hfL2.coeFn_toLp] with x hx
      rw [hx, mul_comm]

end LipschitzWith
