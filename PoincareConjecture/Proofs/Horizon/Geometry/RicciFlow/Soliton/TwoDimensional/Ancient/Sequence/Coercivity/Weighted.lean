import Mathlib.Analysis.SpecialFunctions.Integrals.Basic



set_option autoImplicit false

open Set MeasureTheory

namespace Poincare.Analysis

theorem integral_inv_sqrt_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, 1 / Real.sqrt s) = 2 * Real.sqrt b - 2 * Real.sqrt a := by
  have hcont : ContinuousOn (fun s : ℝ => 1 / Real.sqrt s) (Icc a b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun s hs => (Real.sqrt_pos.2 (ha.trans_le hs.1)).ne')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    (ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hab] using hcont))
  intro s hs
  have hs' : 0 < s := ha.trans_le ((uIcc_of_le hab) ▸ hs).1
  convert! (Real.hasDerivAt_sqrt hs'.ne').const_mul 2 using 1
  field_simp


theorem integral_speed_le_weighted_action
    {f v : ℝ → ℝ} {a b τ C : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ τ)
    (hC : 0 < C) (hf : IntervalIntegrable f volume 0 τ)
    (hf0 : ∀ s ∈ Icc 0 τ, 0 ≤ f s)
    (hv : ContinuousOn v (Icc a b))
    (henergy : ∀ s ∈ Icc a b, Real.sqrt s * v s ^ 2 ≤ f s) :
    (∫ s in a..b, v s) ≤ ((∫ s in 0..τ, f s) + 2 * C ^ 2 * Real.sqrt τ) / (2 * C) := by
  have hτ : 0 ≤ τ := ha.le.trans (hab.trans hb)
  have hfi : IntervalIntegrable f volume a b := hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le hτ]
    exact Icc_subset_Icc ha.le hb)
  have hvi : IntervalIntegrable v volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hv
  have hwi : IntervalIntegrable (fun s : ℝ => 1 / Real.sqrt s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun s hs => (Real.sqrt_pos.2 (ha.trans_le hs.1)).ne')
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      2 * C * v s ≤ f s + C ^ 2 * (1 / Real.sqrt s) := by
    have hw : 0 < Real.sqrt s := Real.sqrt_pos.2 (ha.trans_le hs.1)
    have hsq := sq_nonneg (Real.sqrt s * v s - C)
    have he := mul_le_mul_of_nonneg_left (henergy s hs) hw.le
    have hdiv : Real.sqrt s * (C ^ 2 * (1 / Real.sqrt s)) = C ^ 2 := by
      field_simp
    apply (mul_le_mul_iff_right₀ hw).mp
    nlinarith
  have h := intervalIntegral.integral_mono_on hab (hvi.const_mul (2 * C))
    (hfi.add (hwi.const_mul (C ^ 2))) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hfi (hwi.const_mul (C ^ 2)),
    intervalIntegral.integral_const_mul, integral_inv_sqrt_of_pos ha hab] at h
  have hfull := intervalIntegral.integral_mono_interval ha.le hab hb
    ((ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hf0 s ⟨hs.1.le, hs.2⟩)) hf
  have hsqrt := Real.sqrt_le_sqrt hb
  apply (le_div_iff₀ (by positivity : 0 < 2 * C)).mpr
  nlinarith [Real.sqrt_nonneg a, sq_nonneg C]

end Poincare.Analysis
