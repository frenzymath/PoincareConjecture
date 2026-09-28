import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped intervalIntegral
open scoped Topology

namespace Poincare.Asymptotics


theorem tendsto_elapsed_time_ratio_atBot (a b : ℝ) :
    Tendsto (fun T : ℝ ↦ (a - T) / (b - T)) atBot (𝓝 1) := by
  have hden : Tendsto (fun T : ℝ ↦ b - T) atBot atTop := by
    refine tendsto_atTop.2 (fun C ↦ ?_)
    exact eventually_atBot.2 ⟨b - C, fun T hT ↦ by linarith⟩
  have hsmall : Tendsto (fun T : ℝ ↦ (a - b) / (b - T)) atBot (𝓝 0) :=
    hden.const_div_atTop (a - b)
  have hsum : Tendsto (fun T : ℝ ↦ 1 + (a - b) / (b - T)) atBot (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hsum.congr'
  filter_upwards [eventually_lt_atBot b] with T hT
  have hne : b - T ≠ 0 := ne_of_gt (sub_pos.mpr hT)
  field_simp
  ring


theorem tendsto_div_elapsed_time_atBot (t R : ℝ) :
    Tendsto (fun T : ℝ ↦ R / (t - T)) atBot (𝓝 0) := by
  apply Filter.Tendsto.const_div_atTop
  refine tendsto_atTop.2 (fun C ↦ ?_)
  exact eventually_atBot.2 ⟨t - C, fun T hT ↦ by linarith⟩


theorem nonneg_of_eventually_add_div_nonneg {Q R t : ℝ}
    (hfinite : ∀ᶠ T : ℝ in atBot, 0 ≤ Q + R / (t - T)) :
    0 ≤ Q := by
  have hlim : Tendsto (fun T : ℝ ↦ Q + R / (t - T)) atBot (𝓝 Q) := by
    simpa using (tendsto_div_elapsed_time_atBot t R).const_add Q
  exact ge_of_tendsto hlim hfinite


theorem ancient_limit_of_scaled_inequality
    {a b A B E : ℝ}
    (hfinite : ∀ᶠ T : ℝ in atBot,
      A * (a - T) * E ≤ B * (b - T)) :
    A * E ≤ B := by
  let r : ℝ → ℝ := fun T ↦ (a - T) / (b - T)
  have hr : Tendsto r atBot (𝓝 1) := tendsto_elapsed_time_ratio_atBot a b
  have hleft : Tendsto (fun T ↦ A * r T * E) atBot (𝓝 (A * E)) := by
    simpa [r] using (tendsto_const_nhds.mul hr).mul tendsto_const_nhds
  have hright : Tendsto (fun _ : ℝ ↦ B) atBot (𝓝 B) := tendsto_const_nhds
  have hnorm : ∀ᶠ T : ℝ in atBot, A * r T * E ≤ B := by
    filter_upwards [hfinite, eventually_lt_atBot b] with T hT hTb
    have hpos : 0 < b - T := sub_pos.mpr hTb
    apply (mul_le_mul_iff_left₀ hpos).mp
    have heq : (A * r T * E) * (b - T) = A * (a - T) * E := by
      dsimp [r]
      field_simp
    rwa [heq]
  exact le_of_tendsto_of_tendsto hleft hright hnorm


theorem le_at_right_endpoint {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousWithinAt f (Icc a b) b)
    (hg : ContinuousWithinAt g (Icc a b) b)
    (hfg : ∀ t ∈ Ioo a b, f t ≤ g t) :
    f b ≤ g b := by
  have : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  exact le_of_tendsto_of_tendsto (hf.mono Ioo_subset_Icc_self)
    (hg.mono Ioo_subset_Icc_self)
    ((show ∀ᶠ t : ℝ in 𝓝[Ioo a b] b, t ∈ Ioo a b from
      self_mem_nhdsWithin).mono fun t ht ↦ hfg t ht)


theorem nonneg_at_zero_of_nonneg_neg {f : ℝ → ℝ}
    (hf : ContinuousWithinAt f (Iic 0) 0)
    (hnonneg : ∀ t < 0, 0 ≤ f t) :
    0 ≤ f 0 := by
  exact ge_of_tendsto (hf.mono Iio_subset_Iic_self)
    ((show ∀ᶠ t : ℝ in 𝓝[Iio (0 : ℝ)] 0, t ∈ Iio (0 : ℝ) from
      self_mem_nhdsWithin).mono fun t ht ↦ hnonneg t ht)






theorem le_at_right_endpoint_of_finite_origins
    {f q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hfinite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      f a * (a - T) * Real.exp (-(∫ s in a..t, q s) / 2) ≤
        f t * (t - T)) :
    f a * Real.exp (-(∫ s in a..b, q s) / 2) ≤ f b := by
  have hprimitive : ContinuousOn (fun t ↦ ∫ s in a..t, q s) (Icc a b) := by
    simpa only [uIcc_of_le (le_of_lt hab)] using
      (intervalIntegral.continuousOn_primitive_interval' hqInt left_mem_uIcc)
  let g : ℝ → ℝ := fun t ↦
    f a * Real.exp (-(∫ s in a..t, q s) / 2)
  have hg : ContinuousOn g (Icc a b) := by
    change ContinuousOn (fun t ↦ f a * Real.exp (-(∫ s in a..t, q s) / 2)) (Icc a b)
    exact continuousOn_const.mul
      (Real.continuous_exp.comp_continuousOn
        (hprimitive.neg.div_const 2))
  exact le_at_right_endpoint hab
    (hg b (right_mem_Icc.mpr (le_of_lt hab)))
    (hf b (right_mem_Icc.mpr (le_of_lt hab))) (by
    intro t ht
    exact ancient_limit_of_scaled_inequality (hfinite t ht))


theorem nonneg_at_zero_of_finite_origins {q r : ℝ → ℝ}
    (hq : ContinuousWithinAt q (Iic 0) 0)
    (hfinite : ∀ t < 0, ∀ᶠ T : ℝ in atBot,
      0 ≤ q t + r t / (t - T)) :
    0 ≤ q 0 := by
  apply nonneg_at_zero_of_nonneg_neg hq
  intro t ht
  exact nonneg_of_eventually_add_div_nonneg (hfinite t ht)

end Poincare.Asymptotics
