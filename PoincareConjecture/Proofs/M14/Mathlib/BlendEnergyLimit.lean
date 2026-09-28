import PoincareConjecture.Proofs.M14.Mathlib.BlendEnergyIntegral

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

open Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_integral_shrinking_left {F : ℝ → E} {a b : ℝ} (hab : a < b)
    (hF : IntervalIntegrable F volume a b) :
    Tendsto (fun d => ∫ s in (b - 2 * d)..b, F s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : IntegrableOn F (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hF
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi
  rw [uIcc_of_le hab.le] at hcont
  have hmap : Tendsto (fun d : ℝ => b - 2 * d) (𝓝[>] 0) (𝓝[Icc a b] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h : Continuous (fun d : ℝ => b - 2 * d) :=
        continuous_const.sub (continuous_const.mul continuous_id)
      simpa only [mul_zero, sub_zero] using
        (h.continuousAt (x := 0)).tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (by linarith : 0 < (b - a) / 2)] with d hd
      exact ⟨by linarith [hd.2], by linarith [hd.1]⟩
  have hlim : Tendsto (fun t => ∫ s in t..b, F s) (𝓝[Icc a b] b) (𝓝 0) := by
    simpa only [ContinuousWithinAt, intervalIntegral.integral_same] using hcont b ⟨hab.le, le_rfl⟩
  exact hlim.comp hmap

variable [CompleteSpace E]

theorem tendsto_oneSidedBlend_energy_zero {f g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : DifferentiableOn ℝ f (Ioo a b)) (hdg : DifferentiableOn ℝ g (Ioo a b))
    (hEf : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (hEg : MemLp (deriv g) 2 (volume.restrict (Icc a b)))
    (heq : f b = g b) :
    Tendsto (fun d => ∫ s in (b - 2 * d)..(b - d),
      ‖deriv (smoothJoinBlend f g (b - 3 * d / 2) (d / 2)) s‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hIf : IntervalIntegrable (fun s => ‖deriv f s‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      ((memLp_two_iff_integrable_sq_norm hEf.aestronglyMeasurable).mp hEf)
  have hIg : IntervalIntegrable (fun s => ‖deriv g s‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      ((memLp_two_iff_integrable_sq_norm hEg.aestronglyMeasurable).mp hEg)
  obtain ⟨K, hK, hKb⟩ := exists_smoothJoinCutoff_deriv_bound
  have hbound : Tendsto (fun d => (12 + 48 * K ^ 2) *
      ((∫ s in (b - 2 * d)..b, ‖deriv f s‖ ^ 2) +
        ∫ s in (b - 2 * d)..b, ‖deriv g s‖ ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      ((tendsto_integral_shrinking_left hab hIf).add
        (tendsto_integral_shrinking_left hab hIg)).const_mul (12 + 48 * K ^ 2)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [self_mem_nhdsWithin] with d hd
    exact intervalIntegral.integral_nonneg (by change 0 < d at hd; linarith)
      (fun _ _ => sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (by linarith : 0 < (b - a) / 2)] with d hd
    have hleft : a ≤ b - 2 * d := by linarith [hd.2]
    have hsub : Icc (b - 2 * d) b ⊆ Icc a b := Icc_subset_Icc hleft le_rfl
    exact (oneSidedBlend_energy_le hd.1 hK hKb (hf.mono hsub) (hg.mono hsub)
      (hdf.mono (Ioo_subset_Ioo hleft le_rfl)) (hdg.mono (Ioo_subset_Ioo hleft le_rfl))
      (hEf.mono_measure (Measure.restrict_mono hsub le_rfl))
      (hEg.mono_measure (Measure.restrict_mono hsub le_rfl)) heq).2

end PoincareConjecture.M14
