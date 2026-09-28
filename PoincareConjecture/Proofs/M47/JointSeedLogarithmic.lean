import Mathlib.Analysis.SpecialFunctions.Integrals.Basic










set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M47



theorem jointSeed_age_window {c sigma : ℝ} (hc : 0 < c) (hsigma : 0 < sigma) :
    0 < sigma * Real.exp (-5 / c) ∧ sigma * Real.exp (-5 / c) < sigma := by
  refine ⟨mul_pos hsigma (Real.exp_pos _), ?_⟩
  apply mul_lt_of_lt_one_right hsigma
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by norm_num) hc




theorem jointSeed_scalar_age_of_action
    {d c sigma a eta : ℝ} (hc : 0 < c) (hsigma : 0 < sigma)
    (hsigmaAge : sigma ≤ d / 2) (ha : a = sigma * Real.exp (-5 / c))
    (heta : eta < a) (f r : ℝ → ℝ)
    (hfi : IntervalIntegrable f volume eta d)
    (hf : ∀ v ∈ Icc eta d, 0 ≤ f v)
    (hscalar : ∀ v ∈ Icc a sigma, Real.sqrt (d / 2) * r v ≤ f v)
    (hupper : (∫ v in eta..d, f v) ≤ 3 * Real.sqrt d) :
    ∃ v ∈ Icc a sigma, v * r v ≤ c := by
  have haWindow := jointSeed_age_window hc hsigma
  rw [← ha] at haWindow
  have haPos : 0 < a := haWindow.1
  have haSigma : a ≤ sigma := haWindow.2.le
  have hd : 0 < d := by linarith
  have hsigmaD : sigma ≤ d := by linarith
  have hsmall : Icc a sigma ⊆ Icc eta d := Icc_subset_Icc heta.le hsigmaD
  have hfiSmall : IntervalIntegrable f volume a sigma := hfi.mono_set (by
    rw [uIcc_of_le haSigma, uIcc_of_le (heta.le.trans (haSigma.trans hsigmaD))]
    exact hsmall)
  have hInv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume a sigma :=
    (continuousOn_id.inv₀ (fun v hv => (haPos.trans_le hv.1).ne')).intervalIntegrable_of_Icc
      haSigma
  by_contra hnone
  push Not at hnone
  have hcompare := intervalIntegral.integral_mono_on haSigma
    (hInv.const_mul (Real.sqrt (d / 2) * c)) hfiSmall (fun v hv => by
      have hvPos : 0 < v := haPos.trans_le hv.1
      have hcv : c * v⁻¹ ≤ r v := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ hvPos).2
        nlinarith [hnone v hv]
      exact (show Real.sqrt (d / 2) * c * v⁻¹ ≤ Real.sqrt (d / 2) * r v by
        nlinarith [mul_le_mul_of_nonneg_left hcv (Real.sqrt_nonneg (d / 2))]).trans
          (hscalar v hv))
  have hlog : Real.log (sigma / a) = 5 / c := by
    rw [Real.log_div hsigma.ne' haPos.ne', ha,
      Real.log_mul hsigma.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos haPos hsigma, hlog] at hcompare
  have hcancel : Real.sqrt (d / 2) * c * (5 / c) = 5 * Real.sqrt (d / 2) := by
    field_simp
  rw [hcancel] at hcompare
  have hmono := intervalIntegral.integral_mono_interval heta.le haSigma hsigmaD
    ((ae_restrict_mem measurableSet_Ioc).mono (fun v hv => hf v ⟨hv.1.le, hv.2⟩)) hfi
  have hlarge : 3 * Real.sqrt d < 5 * Real.sqrt (d / 2) := by
    by_contra h
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 5 * Real.sqrt (d / 2))
      (by positivity : 0 ≤ 3 * Real.sqrt d)).2 (le_of_not_gt h)
    nlinarith [Real.sq_sqrt hd.le, Real.sq_sqrt (half_pos hd).le]
  exact (not_lt_of_ge (hcompare.trans (hmono.trans hupper))) hlarge

end PoincareConjecture.M47
