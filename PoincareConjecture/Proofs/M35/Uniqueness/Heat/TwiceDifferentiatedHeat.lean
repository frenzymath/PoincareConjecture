import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DoubleMemoryHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongRecovery










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

theorem exists_twice_differentiated_form_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C D E : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (B : ℝ → V →L[ℝ] V) (hBm : AEStronglyMeasurable B (timeMeasure T))
    (hBb : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D)
    (N : ℝ → V →L[ℝ] V) (hNm : AEStronglyMeasurable N (timeMeasure T))
    (hNb : ∀ᵐ t ∂timeMeasure T, ‖N t‖ ≤ E)
    (hsmall : (T + 1) * (A + D * T + E * (T * T)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (u₀ w₀ z₀ : V) :
    ∃ (u w z : ℝ → V) (Z : ℝ → H), MemLp z 2 (timeMeasure T) ∧
      u 0 = u₀ ∧ w 0 = w₀ ∧ Z 0 = J z₀ ∧
      ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (z t) = Z t) ∧
      (∀ t, w t = w₀ + ∫ s in (0 : ℝ)..t, z s) ∧
      (∀ t, u t = u₀ + ∫ s in (0 : ℝ)..t, w s) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt w (z t) t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (Z t) = J.adjoint (J z₀) +
        ∫ s in (0 : ℝ)..t, R s (z s) + J.adjoint (L s (z s)) +
          B s (w s) + N s (u s) - z s + J.adjoint (J (z s)) := by
  let a : ℝ → V := fun t => w₀ + t • z₀
  let b : ℝ → V := fun t => u₀ + ∫ s in (0 : ℝ)..t, a s
  have hac : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
  have hai : IntervalIntegrable a volume 0 T := hac.intervalIntegrable _ _
  have hbc : ContinuousOn b (Icc 0 T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hai left_mem_uIcc
  let F : ℝ → V := fun t => R t z₀ + J.adjoint (L t z₀) + B t (a t) +
    N t (b t) - z₀ + J.adjoint (J z₀)
  have hF : MemLp F 2 (timeMeasure T) :=
    (((((memLp_timeDependent_fun hRm hRb (memLp_const z₀)).add
      (J.adjoint.comp_memLp' (memLp_timeDependent_fun hLm hLb (memLp_const z₀)))).add
      (memLp_timeDependent_fun hBm hBb (memLp_of_continuousOn_time hac.continuousOn))).add
      (memLp_timeDependent_fun hNm hNb (memLp_of_continuousOn_time hbc))).sub
      (memLp_const z₀)).add (memLp_const (J.adjoint (J z₀)))
  obtain ⟨v, Y, hY0, hYc, hYv, hYi⟩ :=
    exists_double_memory_integral_heat J hc hd hi hn hT hA hC hD hE
      R hRm hRb L hLm hLb B hBm hBb N hNm hNb hsmall (hF.toLp F)
  let z : ℝ → V := fun t => v t + z₀
  let w : ℝ → V := fun t => w₀ + ∫ s in (0 : ℝ)..t, z s
  let u : ℝ → V := fun t => u₀ + ∫ s in (0 : ℝ)..t, w s
  let p : ℝ → V := fun t => ∫ s in (0 : ℝ)..t, v s
  have hz : MemLp z 2 (timeMeasure T) := (Lp.memLp v).add (memLp_const z₀)
  have hzi : IntervalIntegrable z volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hz.integrable (by norm_num))
  have hvi : IntervalIntegrable (fun s => v s) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((Lp.memLp v).integrable (by norm_num))
  have hpc : ContinuousOn p (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hvi left_mem_uIcc
  have hwc : ContinuousOn w (Icc 0 T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hzi left_mem_uIcc
  have hwi : IntervalIntegrable w volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((memLp_of_continuousOn_time hwc).integrable (by norm_num))
  have huc : ContinuousOn u (Icc 0 T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hwi left_mem_uIcc
  have hwp {t : ℝ} (ht : t ∈ Icc 0 T) : w t = a t + p t := by
    have hvit : IntervalIntegrable (fun s => v s) volume 0 t := hvi.mono_set (by
      simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
    dsimp only [w, z, a, p]
    rw [intervalIntegral.integral_add hvit intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    abel
  have hup {t : ℝ} (ht : t ∈ Icc 0 T) :
      u t = b t + ∫ s in (0 : ℝ)..t, p s := by
    have hpit : IntervalIntegrable p volume 0 t :=
      (hpc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have he : (∫ s in (0 : ℝ)..t, w s) = ∫ s in (0 : ℝ)..t, a s + p s := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply hwp
      exact (by simpa only [uIcc_of_le ht.1] using hs : s ∈ Icc 0 t) |>.imp_right
        (fun h => h.trans ht.2)
    dsimp only [u, b]
    rw [he, intervalIntegral.integral_add (hac.intervalIntegrable _ _) hpit]
    abel
  refine ⟨u, w, z, fun t => Y t + J z₀, hz, ?_, ?_, ?_, huc, hwc,
    hYc.add continuousOn_const, ?_, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · simp only [u, intervalIntegral.integral_same, add_zero]
  · simp only [w, intervalIntegral.integral_same, add_zero]
  · change Y 0 + J z₀ = J z₀
    rw [hY0, zero_add]
  · filter_upwards [hYv] with t ht
    rw [map_add, ht]
  · intro t ht
    exact hasDerivWithinAt_volterraPath_Icc hwc ht
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hzi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT] using Ioc_subset_Icc_self hmem)
      0 left_mem_uIcc).const_add w₀
  · intro t ht
    rw [map_add, hYi t ht, add_comm _ (J.adjoint (J z₀))]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl ht.2) hF.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hst.1.le, hst.2.trans ht.2⟩
    rw [hs, hwp hsT, hup hsT]
    dsimp only [F, z, p]
    simp only [map_add]
    abel

end PoincareConjecture.M35.Uniqueness.Heat
