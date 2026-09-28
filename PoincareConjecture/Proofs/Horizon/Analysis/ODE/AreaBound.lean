import PoincareConjecture.Proofs.Horizon.Analysis.ODE.ScalarComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue









set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace Poincare.ODE



theorem le_mul_exp_of_integral_le_of_deriv_le_mul
    {A A' : ℝ → ℝ} {a m b K V : ℝ}
    (ham : a < m) (hmb : m ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ A x)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt A (A' x) x)
    (hbound : ∀ x ∈ Ioo a b, A' x ≤ K * A x)
    (hmass : (∫ x in a..b, A x) ≤ V) :
    ∀ t ∈ Icc m b,
      A t ≤ V / (m - a) * Real.exp (max K 0 * (b - a)) := by
  have hcont_am : ContinuousOn A (Icc a m) :=
    hcont.mono (Icc_subset_Icc le_rfl hmb)
  obtain ⟨s, hs, hmean⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (a := a) (b := m) (f := A) (g := fun _ => (1 : ℝ)) (μ := volume)
    (by simpa only [uIcc_of_le ham.le] using hcont_am)
    intervalIntegrable_const (fun _ _ => zero_le_one)
  have hs_am : s ∈ Icc a m := by simpa only [uIcc_of_le ham.le] using hs
  have hs_ab : s ∈ Icc a b := ⟨hs_am.1, hs_am.2.trans hmb⟩
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at hmean
  have hsmall : (∫ x in a..m, A x) ≤ V := by
    refine (intervalIntegral.integral_mono_interval le_rfl ham.le hmb ?_
      (hcont.intervalIntegrable_of_Icc (ham.le.trans hmb))).trans hmass
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hnonneg x ⟨hx.1.le, hx.2⟩
  have hs_bound : A s ≤ V / (m - a) := by
    apply (le_div_iff₀ (sub_pos.mpr ham)).2
    exact hmean.symm.trans_le hsmall
  intro t ht
  have hst : s ≤ t := hs_am.2.trans ht.1
  have hsub {x : ℝ} (hx : x ∈ Ioo s t) : x ∈ Ioo a b :=
    ⟨hs_am.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
  have hcompare : A t ≤ A s * Real.exp (K * (t - s)) := by
    have h := mul_exp_neg_integral_le_of_deriv_add_mul_nonneg hst
      (f := fun x => -A x) (f' := fun x => -A' x) (q := fun _ => -K)
      (hcont.neg.mono (Icc_subset_Icc hs_am.1 ht.2))
      continuousOn_const intervalIntegrable_const
      (fun x hx => (hderiv x (hsub hx)).neg)
      (by
        intro x hx
        nlinarith only [hbound x (hsub hx)])
    have hexponent : -(∫ _ in s..t, -K) = K * (t - s) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexponent, neg_mul, neg_le_neg_iff] at h
    exact h
  have hexponent : K * (t - s) ≤ max K 0 * (b - a) := by
    calc
      K * (t - s) ≤ max K 0 * (t - s) :=
        mul_le_mul_of_nonneg_right (le_max_left K 0) (sub_nonneg.mpr hst)
      _ ≤ max K 0 * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2, hs_am.1]) (le_max_right K 0)
  calc
    A t ≤ A s * Real.exp (K * (t - s)) := hcompare
    _ ≤ A s * Real.exp (max K 0 * (b - a)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (hnonneg s hs_ab)
    _ ≤ V / (m - a) * Real.exp (max K 0 * (b - a)) :=
      mul_le_mul_of_nonneg_right hs_bound (Real.exp_pos _).le

end Poincare.ODE
