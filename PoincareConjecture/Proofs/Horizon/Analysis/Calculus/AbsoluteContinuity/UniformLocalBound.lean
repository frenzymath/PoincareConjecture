import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Poincare.Analysis

theorem abs_sub_le_of_uniform_local_lipschitz_on_interval
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (D : ℝ≥0)
    (hf : ∀ t ∈ Icc a b, ∃ U ∈ 𝓝[Icc a b] t, LipschitzOnWith D f U) :
    |f b - f a| ≤ D * (b - a) := by
  have hloc : LocallyLipschitzOn (Icc a b) f := fun t ht => ⟨D, hf t ht⟩
  obtain ⟨C, hC⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hAC : AbsolutelyContinuousOnInterval f a b :=
    (show LipschitzOnWith C f (uIcc a b) by rwa [uIcc_of_le hab]).absolutelyContinuousOnInterval
  have hd : ∀ᵐ t ∂volume.restrict (Icc a b), |deriv f t| ≤ D := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    obtain ⟨U, hU, hlip⟩ := hf t ⟨ht.1.le, ht.2.le⟩
    rw [(nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2))] at hU
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitzOn hU hlip
  calc
    _ = |∫ t in a..b, deriv f t| := by rw [hAC.integral_deriv_eq_sub]
    _ ≤ ∫ t in a..b, |deriv f t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ _t in a..b, (D : ℝ) := intervalIntegral.integral_mono_ae_restrict hab
      hAC.intervalIntegrable_deriv.abs intervalIntegrable_const hd
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

end Poincare.Analysis
