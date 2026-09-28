import Mathlib.MeasureTheory.Integral.DominatedConvergence









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem tendsto_integral_upper_from_left {F : ℝ → E} {a b k : ℝ}
    (hab : a < b) (hF : IntervalIntegrable F volume a b) (hk : 0 < k) :
    Tendsto (fun d => ∫ s in a..(b - k * d), F s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s in a..b, F s)) := by
  have hi : IntegrableOn F (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hF
  have hcont := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le hab.le] at hcont
  have hmap : Tendsto (fun d : ℝ => b - k * d) (𝓝[>] 0) (𝓝[Icc a b] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h : Continuous (fun d : ℝ => b - k * d) :=
        continuous_const.sub (continuous_const.mul continuous_id)
      simpa only [mul_zero, sub_zero] using
        (h.continuousAt (x := 0)).tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (div_pos (sub_pos.mpr hab) hk)] with d hd
      have hsmall := (lt_div_iff₀ hk).mp hd.2
      exact ⟨by nlinarith, by nlinarith [mul_pos hk hd.1]⟩
  exact (hcont b ⟨hab.le, le_rfl⟩).tendsto.comp hmap



theorem tendsto_integral_lower_at_interior {F : ℝ → E} {a b c : ℝ}
    (hF : IntervalIntegrable F volume a b) (hc : c ∈ Ioo a b) (k : ℝ) :
    Tendsto (fun d => ∫ s in (c - k * d)..b, F s)
      (𝓝 (0 : ℝ)) (𝓝 (∫ s in c..b, F s)) := by
  have hab : a ≤ b := (hc.1.trans hc.2).le
  have hi : IntegrableOn F (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hF
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi
  rw [uIcc_of_le hab] at hcont
  have h := (hcont c (Ioo_subset_Icc_self hc)).continuousAt (Icc_mem_nhds hc.1 hc.2)
  have hm : Continuous (fun d : ℝ => c - k * d) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hmap : Tendsto (fun d : ℝ => c - k * d) (𝓝 0) (𝓝 c) := by
    simpa only [mul_zero, sub_zero] using (hm.continuousAt (x := 0)).tendsto
  exact h.tendsto.comp hmap

end PoincareConjecture.M14
