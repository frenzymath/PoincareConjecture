import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

namespace Poincare

theorem tendsto_of_ball_volume_radius_squeeze
    {f : ℕ → ℝ≥0∞} {V : ℝ → ℝ≥0∞} {r : ℝ} (n : ℕ)
    (hV : ContinuousAt V r)
    (hupper : ∀ C : ℝ, 1 < C → ∀ᶠ k in atTop,
      f k ≤ ENNReal.ofReal C ^ n * V (C * r))
    (hlower : ∀ C : ℝ, 1 < C → ∀ᶠ k in atTop,
      V (r / C) ≤ ENNReal.ofReal C ^ n * f k) :
    Tendsto f atTop (𝓝 (V r)) := by
  have hpower : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one, one_pow] using
      ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal).tendsto 1
  have hmul : Tendsto (fun C : ℝ => C * r) (𝓝 1) (𝓝 r) := by
    have h : ContinuousAt (fun C : ℝ => C * r) 1 := by fun_prop
    simpa only [one_mul] using h.tendsto
  have hdiv : Tendsto (fun C : ℝ => r / C) (𝓝 1) (𝓝 r) := by
    have h : ContinuousAt (fun C : ℝ => r / C) 1 := by fun_prop (disch := norm_num)
    simpa only [div_one] using h.tendsto
  have hU : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n * V (C * r))
      (𝓝 1) (𝓝 (V r)) := by
    simpa using ENNReal.Tendsto.mul hpower (Or.inl one_ne_zero)
      (hV.tendsto.comp hmul) (Or.inr ENNReal.one_ne_top)
  have hL : Tendsto (fun C : ℝ => V (r / C) / ENNReal.ofReal C ^ n)
      (𝓝 1) (𝓝 (V r)) := by
    simpa using ENNReal.Tendsto.div (hV.tendsto.comp hdiv) (Or.inr one_ne_zero)
      hpower (Or.inl ENNReal.one_ne_top)
  have hCevent : ∀ᶠ C : ℝ in 𝓝[>] 1, 1 < C := self_mem_nhdsWithin
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨C, hC, haC⟩ := (hCevent.and
      ((hL.eventually_const_lt ha).filter_mono nhdsWithin_le_nhds)).exists
    filter_upwards [hlower C hC] with k hk
    apply haC.trans_le
    exact (ENNReal.div_le_iff'
      (pow_ne_zero n (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hC)))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mpr hk
  · intro b hb
    obtain ⟨C, hC, hCb⟩ := (hCevent.and
      ((hU.eventually_lt_const hb).filter_mono nhdsWithin_le_nhds)).exists
    filter_upwards [hupper C hC] with k hk
    exact hk.trans_lt hCb

end Poincare
