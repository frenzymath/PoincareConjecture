import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MemoryHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.BochnerAbsolute

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem exists_differentiated_form_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C D : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (B : ℝ → V →L[ℝ] V) (hBm : AEStronglyMeasurable B (timeMeasure T))
    (hBb : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D)
    (hsmall : (T + 1) * (A + D * T) + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (u₀ w₀ : V) :
    ∃ (u w : ℝ → V) (W : ℝ → H), MemLp w 2 (timeMeasure T) ∧
      u 0 = u₀ ∧ W 0 = J w₀ ∧ ContinuousOn u (Icc 0 T) ∧ ContinuousOn W (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (w t) = W t) ∧
      (∀ t, u t = u₀ + ∫ s in (0 : ℝ)..t, w s) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt u (w t) t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (W t) = J.adjoint (J w₀) +
        ∫ s in (0 : ℝ)..t, R s (w s) + J.adjoint (L s (w s)) +
          B s (u s) - w s + J.adjoint (J (w s)) := by
  let a : ℝ → V := fun t => u₀ + t • w₀
  have ha : MemLp a 2 (timeMeasure T) := by
    have hac : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
    apply MemLp.of_bound hac.aestronglyMeasurable (‖u₀‖ + T * ‖w₀‖)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (norm_add_le _ _).trans (add_le_add le_rfl (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
      exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)))
  let F : ℝ → V := fun t => R t w₀ + J.adjoint (L t w₀) + B t (a t) -
    w₀ + J.adjoint (J w₀)
  have hF : MemLp F 2 (timeMeasure T) :=
    ((((memLp_timeDependent_fun hRm hRb (memLp_const w₀)).add
      (J.adjoint.comp_memLp' (memLp_timeDependent_fun hLm hLb (memLp_const w₀)))).add
      (memLp_timeDependent_fun hBm hBb ha)).sub (memLp_const w₀)).add
        (memLp_const (J.adjoint (J w₀)))
  obtain ⟨z, Z, hZ0, hZc, hZz, hZi⟩ :=
    exists_memory_integral_heat J hc hd hi hn hT hA hC hD
      R hRm hRb L hLm hLb B hBm hBb hsmall (hF.toLp F)
  let w : ℝ → V := fun t => z t + w₀
  let u : ℝ → V := fun t => u₀ + ∫ s in (0 : ℝ)..t, w s
  have hw : MemLp w 2 (timeMeasure T) := (Lp.memLp z).add (memLp_const w₀)
  have hwi : IntervalIntegrable w volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hw.integrable (by norm_num))
  have huc : ContinuousOn u (Icc 0 T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hwi left_mem_uIcc
  have huz {s : ℝ} (hs : s ∈ Icc 0 T) :
      u s = a s + ∫ r in (0 : ℝ)..s, z r := by
    have hzi : IntervalIntegrable (fun r => z r) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).mpr
        ((show IntegrableOn (fun r => z r) (Ioc 0 T) volume from
          (Lp.memLp z).integrable (by norm_num)).mono_set (Ioc_subset_Ioc le_rfl hs.2))
    dsimp only [u, w, a]
    rw [intervalIntegral.integral_add hzi intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    abel
  refine ⟨u, w, fun t => Z t + J w₀, hw, ?_, ?_, huc,
    hZc.add continuousOn_const, ?_, fun _ => rfl, ?_, ?_⟩
  · simp only [u, intervalIntegral.integral_same, add_zero]
  · change Z 0 + J w₀ = J w₀
    rw [hZ0, zero_add]
  · filter_upwards [hZz] with t ht
    rw [map_add, ht]
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hwi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT] using Ioc_subset_Icc_self hmem)
      0 left_mem_uIcc).const_add u₀
  · intro t ht
    rw [map_add, hZi t ht, add_comm _ (J.adjoint (J w₀))]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl ht.2) hF.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hst.1.le, hst.2.trans ht.2⟩
    rw [hs, huz hsT]
    dsimp only [F, w]
    simp only [map_add]
    abel

end PoincareConjecture.M35.Uniqueness.Heat
