import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M65

theorem abs_sq_sub_sq_le_weighted_mass {f v : ℝ → ℝ} {a b K : ℝ}
    (hf : Differentiable ℝ f) (hv : Continuous v) (hK : 0 ≤ K)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hv0 : ∀ x ∈ Icc a b, 0 ≤ v x)
    (hderiv : ∀ x ∈ Icc a b, |deriv f x| ≤ K * v x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x ^ 2 - f y ^ 2| ≤ 2 * K * ∫ z in a..b, f z * v z := by
  have hnonneg : ∀ z ∈ Icc a b, 0 ≤ 2 * K * (f z * v z) := by
    intro z hz
    exact mul_nonneg (by positivity) (mul_nonneg (hf0 z hz) (hv0 z hz))
  have hcont : Continuous (fun z => 2 * K * (f z * v z)) :=
    continuous_const.mul (hf.continuous.mul hv)
  have hbound : ∀ z ∈ Icc a b, ‖deriv (fun r => f r ^ 2) z‖ ≤
      2 * K * (f z * v z) := by
    intro z hz
    have hfz := hf0 z hz
    have heq : deriv (fun r => f r ^ 2) z = 2 * f z * deriv f z := by
      simpa using ((hf z).hasDerivAt.fun_pow 2).deriv
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * f z)]
    calc
      2 * f z * |deriv f z| ≤ 2 * f z * (K * v z) :=
        mul_le_mul_of_nonneg_left (hderiv z hz) (by positivity)
      _ = 2 * K * (f z * v z) := by ring
  have hordered : ∀ {p q : ℝ}, p ∈ Icc a b → q ∈ Icc a b → p ≤ q →
      |f q ^ 2 - f p ^ 2| ≤ 2 * K * ∫ z in a..b, f z * v z := by
    intro p q hp hq hpq
    have hsub : Icc p q ⊆ Icc a b := Icc_subset_Icc hp.1 hq.2
    have hfirst := norm_sub_le_integral_of_norm_deriv_le_of_le hpq
      (hf.continuous.fun_pow 2).continuousOn (hf.fun_pow 2).differentiableOn
      (Filter.Eventually.of_forall (fun z hz => hbound z (hsub (Ioo_subset_Icc_self hz))))
      (hcont.intervalIntegrable p q)
    have hsecond := intervalIntegral.integral_mono_interval (μ := volume) hp.1 hpq hq.2
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun z hz => hnonneg z (Ioc_subset_Icc_self hz))))
      (hcont.intervalIntegrable a b)
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using
      hfirst.trans hsecond
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    exact hordered hx hy hxy
  · exact hordered hy hx hyx

theorem sq_le_weighted_average_sq_add_mass {f v : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (hf : Differentiable ℝ f) (hv : Continuous v) (hK : 0 ≤ K)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hv0 : ∀ x ∈ Icc a b, 0 ≤ v x)
    (hderiv : ∀ x ∈ Icc a b, |deriv f x| ≤ K * v x)
    (hL : 0 < ∫ z in a..b, v z) {x : ℝ} (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ ((∫ z in a..b, f z * v z) / (∫ z in a..b, v z)) ^ 2 +
      2 * K * ∫ z in a..b, f z * v z := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    hf.continuous.continuousOn
  have hmin_integral := intervalIntegral.integral_mono_on (μ := volume) hab
    (((continuous_const : Continuous (fun _ : ℝ => f y)).mul hv).intervalIntegrable a b)
    ((hf.continuous.mul hv).intervalIntegrable a b)
    (fun z hz => mul_le_mul_of_nonneg_right (hmin hz) (hv0 z hz))
  change (∫ u in a..b, f y * v u) ≤ ∫ u in a..b, f u * v u at hmin_integral
  rw [intervalIntegral.integral_const_mul] at hmin_integral
  have havg : f y ≤ (∫ z in a..b, f z * v z) / (∫ z in a..b, v z) :=
    (le_div_iff₀ hL).mpr hmin_integral
  have hsquare := pow_le_pow_left₀ (hf0 y hy) havg 2
  have hosc := abs_sq_sub_sq_le_weighted_mass hf hv hK hf0 hv0 hderiv hx hy
  linarith [le_abs_self (f x ^ 2 - f y ^ 2)]

end PoincareConjecture.M65
