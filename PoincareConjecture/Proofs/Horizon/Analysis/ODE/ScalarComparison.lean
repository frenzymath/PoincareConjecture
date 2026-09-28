import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
















set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace Poincare.ODE


theorem mul_exp_neg_integral_le_of_deriv_add_mul_nonneg
    {a b : ℝ} (hab : a ≤ b) {f f' q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, 0 ≤ f' t + q t * f t) :
    f a * Real.exp (-(∫ t in a..b, q t)) ≤ f b := by
  let Q : ℝ → ℝ := fun t ↦ ∫ s in a..t, q s
  have hQ : ContinuousOn Q (Icc a b) := by
    simpa only [Q, uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hqInt left_mem_uIcc)
  have hQ' (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt Q (q t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hqInt.mono_set (uIcc_subset_uIcc_left (by
        simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self ht))
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hq t ht
    · exact hq.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hprod (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s ↦ f s * Real.exp (Q s))
        ((f' t + q t * f t) * Real.exp (Q t)) t := by
    convert! (hf' t ht).mul (hQ' t ht).exp using 1
    ring
  have hmono : MonotoneOn (fun t ↦ f t * Real.exp (Q t)) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (hf.mul (Real.continuous_exp.comp_continuousOn hQ))
    · intro t ht
      exact (hprod t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonneg (hineq t (by simpa only [interior_Icc] using ht))
        (Real.exp_pos _).le
  have hend := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  change f a * Real.exp (Q a) ≤ f b * Real.exp (Q b) at hend
  have hstart : Q a = 0 := by simp [Q]
  rw [hstart, Real.exp_zero, mul_one] at hend
  calc
    f a * Real.exp (-Q b) ≤ (f b * Real.exp (Q b)) * Real.exp (-Q b) :=
      mul_le_mul_of_nonneg_right hend (Real.exp_pos _).le
    _ = f b := by rw [mul_assoc, ← Real.exp_add]; simp


theorem finite_harnack_of_deriv_inequality
    {T a b : ℝ} (hTa : T < a) (hab : a ≤ b) {f f' q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, 0 ≤ f' t + f t / (t - T) + q t * f t) :
    f a * (a - T) * Real.exp (-(∫ t in a..b, q t)) ≤ f b * (b - T) := by
  apply mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hab
    (hf.mul (continuousOn_id.sub continuousOn_const)) hq hqInt
    (f' := fun t ↦ f' t * (t - T) + f t)
  · intro t ht
    convert! (hf' t ht).mul ((hasDerivAt_id t).sub_const T) using 1
    simp only [id_eq, mul_one]
  · intro t ht
    have htT : 0 < t - T := sub_pos.mpr (hTa.trans ht.1)
    have h := mul_nonneg (hineq t ht) htT.le
    have heq :
        (f' t + f t / (t - T) + q t * f t) * (t - T) =
          f' t * (t - T) + f t + q t * (f t * (t - T)) := by
      field_simp [htT.ne']
    rwa [heq] at h


theorem harnack_of_energy_inequality
    {a b : ℝ} (hab : a ≤ b) {f f' speedSq : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hSpeed : ContinuousOn speedSq (Ioo a b))
    (hSpeedInt : IntervalIntegrable speedSq volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b, 0 ≤ f' t + speedSq t / 2 * f t) :
    f a * Real.exp (-(∫ t in a..b, speedSq t) / 2) ≤ f b := by
  simpa only [intervalIntegral.integral_div, neg_div] using
    mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hab hf (hSpeed.div_const 2)
      (hSpeedInt.div_const 2) hf' hineq


theorem finite_harnack_of_energy_inequality
    {T a b : ℝ} (hTa : T < a) (hab : a ≤ b) {f f' speedSq : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hSpeed : ContinuousOn speedSq (Ioo a b))
    (hSpeedInt : IntervalIntegrable speedSq volume a b)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Ioo a b,
      0 ≤ f' t + f t / (t - T) + speedSq t / 2 * f t) :
    f a * (a - T) * Real.exp (-(∫ t in a..b, speedSq t) / 2) ≤ f b * (b - T) := by
  simpa only [intervalIntegral.integral_div, neg_div] using
    finite_harnack_of_deriv_inequality hTa hab hf (hSpeed.div_const 2)
      (hSpeedInt.div_const 2) hf' hineq

end Poincare.ODE
