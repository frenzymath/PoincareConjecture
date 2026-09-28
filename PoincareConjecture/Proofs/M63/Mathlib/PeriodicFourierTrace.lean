import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open Set MeasureTheory AddCircle
open scoped ENNReal

namespace PoincareConjecture.M63




theorem memℓp_fourierCoeffOn {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) : Memℓp (fourierCoeffOn hab f) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simpa using (hasSum_sq_fourierCoeffOn hab hf).summable




theorem fourierCoeffOn_derivative {a b : ℝ} (hab : a < b) {f f1 : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f1 x) x) (hcont : Continuous f1)
    (hboundary : f b = f a) (n : ℤ) :
    fourierCoeffOn hab f1 n =
      Complex.I * ((2 * Real.pi * (n : ℝ) / (b - a) : ℝ) : ℂ) * fourierCoeffOn hab f n := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero,
      zero_div, Complex.ofReal_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable a b), hboundary, sub_self, smul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hderiv x)
      (hcont.intervalIntegrable a b)
    simp only [hboundary, sub_self, mul_zero, zero_sub] at h
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hLC : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hab.ne')
    apply (mul_left_cancel₀ hLC)
    push_cast
    field_simp [hLC, sub_ne_zero.mpr (by exact_mod_cast hab.ne' : (b : ℂ) ≠ a)]
    field_simp [hnC, hpiC, Complex.I_ne_zero] at h
    linear_combination -h




theorem fourierCoeffOn_second_weight {a b : ℝ} (hab : a < b) {f f1 f2 : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f1 x) x) (hderiv1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hcont1 : Continuous f1) (hcont2 : Continuous f2)
    (hboundary : f b = f a) (hboundary1 : f1 b = f1 a) :
    (∀ n : ℤ, ((1 + (2 * Real.pi * (n : ℝ) / (b - a)) ^ 2 : ℝ) : ℂ) *
      fourierCoeffOn hab f n = fourierCoeffOn hab f n - fourierCoeffOn hab f2 n) ∧
    Memℓp (fun n : ℤ => ((1 + (2 * Real.pi * (n : ℝ) / (b - a)) ^ 2 : ℝ) : ℂ) *
      fourierCoeffOn hab f n) 2 := by
  have hcoeff (n : ℤ) : ((1 + (2 * Real.pi * (n : ℝ) / (b - a)) ^ 2 : ℝ) : ℂ) *
      fourierCoeffOn hab f n = fourierCoeffOn hab f n - fourierCoeffOn hab f2 n := by
    rw [fourierCoeffOn_derivative hab hderiv1 hcont2 hboundary1,
      fourierCoeffOn_derivative hab hderiv hcont1 hboundary]
    push_cast
    linear_combination (fourierCoeffOn hab f n *
      (2 * (Real.pi : ℂ) * n / ((b : ℂ) - a)) ^ 2) * Complex.I_sq
  refine ⟨hcoeff, ?_⟩
  have hm (g : ℝ → ℂ) (hg : Continuous g) :
      MemLp g 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
      ((hg.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hfcont : Continuous f :=
    (show Differentiable ℝ f from fun x => (hderiv x).differentiableAt).continuous
  have hsub := (memℓp_fourierCoeffOn hab (hm f hfcont)).sub
    (memℓp_fourierCoeffOn hab (hm f2 hcont2))
  change Memℓp (fun n => fourierCoeffOn hab f n - fourierCoeffOn hab f2 n) 2 at hsub
  simpa only [← hcoeff] using hsub




theorem memℓp_second_weight_of_contDiff_periodic {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hperiod : Function.Periodic f L) :
    Memℓp (fun n : ℤ => ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
      fourierCoeffOn hL f n) 2 := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv' (n := 1)
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hd1 (x : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (hf1.differentiable (by norm_num) x).hasDerivAt
  have hboundary : f L = f 0 := by simpa using hperiod 0
  have htranslate : (fun x => f (x + L)) = f := funext hperiod
  have hshift := (hd (0 + L)).scomp 0 ((hasDerivAt_id (0 : ℝ)).add_const L)
  simp only [zero_add, one_smul, Function.comp_def, id_eq] at hshift
  rw [htranslate] at hshift
  have hboundary1 : deriv f L = deriv f 0 := hshift.unique (hd 0)
  simpa only [sub_zero] using
    (fourierCoeffOn_second_weight hL hd hd1 hf1.continuous
      (hf1.continuous_deriv (by norm_num)) hboundary hboundary1).2

end PoincareConjecture.M63
