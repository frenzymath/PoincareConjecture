import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondTimeCompatibility
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TwiceDifferentiatedHeat










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

omit [CompleteSpace V] in
private theorem continuous_operator_memLp {T : ℝ}
    (A : ℝ → V →L[ℝ] V) (hA : ContinuousOn A (Icc 0 T))
    (v : ℝ → V) (hv : MemLp v 2 (timeMeasure T)) :
    MemLp (fun t => A t (v t)) 2 (timeMeasure T) := by
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  have hAm : AEStronglyMeasurable A (timeMeasure T) :=
    (hA.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hAb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC t (Ioc_subset_Icc_self ht)
  exact memLp_timeDependent_fun hAm hAb hv

theorem twice_heat_recovery (J : V →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T)
    (K K₁ K₂ : ℝ → V →L[ℝ] V)
    (hK : ContDiffOn ℝ 1 K (Icc 0 T)) (hK₁ : ContDiffOn ℝ 1 K₁ (Icc 0 T))
    (hK₂ : ContinuousOn K₂ (Icc 0 T))
    (hKd : ∀ t ∈ Ioo 0 T, HasDerivAt K (K₁ t) t)
    (hK₁d : ∀ t ∈ Ioo 0 T, HasDerivAt K₁ (K₂ t) t)
    (u w z : ℝ → V) (Z : ℝ → H) (u₀ w₀ z₀ : V)
    (hz : MemLp z 2 (timeMeasure T))
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hZ : ContinuousOn Z (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, J (z t) = Z t)
    (hwi : ∀ t, w t = w₀ + ∫ s in (0 : ℝ)..t, z s)
    (hui : ∀ t, u t = u₀ + ∫ s in (0 : ℝ)..t, w s)
    (hZi : ∀ t ∈ Icc 0 T, J.adjoint (Z t) = J.adjoint (J z₀) +
      ∫ s in (0 : ℝ)..t, -K s (z s) - K₁ s (w s) - K₁ s (w s) - K₂ s (u s))
    (hcompat : J.adjoint (J w₀) + K 0 u₀ = 0)
    (hcompat₁ : J.adjoint (J z₀) + K 0 w₀ + K₁ 0 u₀ = 0) :
    (∀ t ∈ Icc 0 T, J.adjoint (J (w t)) + K t (u t) = 0) ∧
      (∀ t ∈ Icc 0 T, J.adjoint (Z t) + K t (w t) + K₁ t (u t) = 0) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => J (w s)) (Z t) (Icc 0 T) t := by
  have hzm : IntervalIntegrable z volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hz.integrable (by norm_num))
  have hwm : IntervalIntegrable w volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((memLp_of_continuousOn_time hw).integrable (by norm_num))
  let q : ℝ → V := fun t => -K t (z t) - K₁ t (w t) - K₁ t (w t) - K₂ t (u t)
  have hq : MemLp q 2 (timeMeasure T) :=
    (((continuous_operator_memLp K hK.continuousOn z hz).neg.sub
      (continuous_operator_memLp K₁ hK₁.continuousOn w
        (memLp_of_continuousOn_time hw))).sub
      (continuous_operator_memLp K₁ hK₁.continuousOn w
        (memLp_of_continuousOn_time hw))).sub
      (continuous_operator_memLp K₂ hK₂ u (memLp_of_continuousOn_time hu))
  have hqm : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hq.integrable (by norm_num))
  have hsecond : ∀ t ∈ Icc 0 T,
      J.adjoint (Z t) + K t (w t) + K₁ t (u t) = 0 := by
    have hr := moving_operator_second_compatibility hT K K₁ K₂ hK hK₁ hKd hK₁d
      u w z q u₀ w₀ (J.adjoint (J z₀)) hzm hwm hqm hwi hui hcompat₁ (by
        filter_upwards with t
        dsimp only [q]
        abel)
    intro t ht
    rw [hZi t ht]
    exact hr t ht
  have hJw (t : ℝ) (ht : t ∈ Icc 0 T) :
      J (w t) = J w₀ + ∫ s in (0 : ℝ)..t, Z s := by
    have hzt : IntervalIntegrable z volume 0 t := hzm.mono_set (by
      simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
    rw [hwi t, map_add, ← J.intervalIntegral_comp_comm hzt]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hgraph
  have hZint : IntervalIntegrable Z volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      ((memLp_of_continuousOn_time hZ).integrable (by norm_num))
  have horiginal := moving_operator_compatibility hT K K₁ hK hKd
    w (fun t => J.adjoint (Z t)) hwm
    ((J.adjoint.continuous.comp_continuousOn hZ).intervalIntegrable_of_Icc hT)
    u₀ (J.adjoint (J w₀)) hcompat (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [← hui t]
      have he := hsecond t (Ioc_subset_Icc_self ht)
      convert he using 1
      abel)
  refine ⟨?_, hsecond, ?_⟩
  · intro t ht
    have hZt : IntervalIntegrable Z volume 0 t := hZint.mono_set (by
      simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
    rw [hJw t ht, map_add, ← J.adjoint.intervalIntegral_comp_comm hZt, hui t]
    exact horiginal t ht
  · intro t ht
    exact (hasDerivWithinAt_volterraPath_Icc hZ ht).congr_of_mem hJw ht

end PoincareConjecture.M35.Uniqueness.Heat
