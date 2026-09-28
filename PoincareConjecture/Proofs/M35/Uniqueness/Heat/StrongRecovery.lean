import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeCompatibility
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DifferentiatedHeat











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

theorem memLp_of_continuousOn_time {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : ℝ → E} (hf : ContinuousOn f (Icc 0 T)) :
    MemLp f 2 (timeMeasure T) := by
  let : SecondCountableTopologyEither ℝ E := ⟨Or.inl inferInstance⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t (Ioc_subset_Icc_self ht)

theorem strong_heat_recovery (J : V →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T)
    (K B : ℝ → V →L[ℝ] V) (hK : ContDiffOn ℝ 1 K (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T))
    (hKd : ∀ t ∈ Ioo 0 T, HasDerivAt K (-B t) t)
    (u w : ℝ → V) (W : ℝ → H) (u₀ w₀ : V)
    (hw : MemLp w 2 (timeMeasure T)) (hu : ContinuousOn u (Icc 0 T))
    (hW : ContinuousOn W (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, J (w t) = W t)
    (hui : ∀ t, u t = u₀ + ∫ s in (0 : ℝ)..t, w s)
    (hWi : ∀ t ∈ Icc 0 T, J.adjoint (W t) = J.adjoint (J w₀) +
      ∫ s in (0 : ℝ)..t, -K s (w s) + B s (u s))
    (hcompat : J.adjoint (J w₀) + K 0 u₀ = 0) :
    (∀ t ∈ Icc 0 T, J.adjoint (W t) + K t (u t) = 0) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => J (u s)) (W t) (Icc 0 T) t := by
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  have hKm : AEStronglyMeasurable K (timeMeasure T) :=
    (hK.continuousOn.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hBm : AEStronglyMeasurable B (timeMeasure T) :=
    (hB.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hK.continuousOn
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hCb : ∀ᵐ t ∂timeMeasure T, ‖K t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC t (Ioc_subset_Icc_self ht)
  have hDb : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hD t (Ioc_subset_Icc_self ht)
  let q : ℝ → V := fun t => -K t (w t) + B t (u t)
  have hq : MemLp q 2 (timeMeasure T) :=
    (memLp_timeDependent_fun hKm hCb hw).neg.add
      (memLp_timeDependent_fun hBm hDb (memLp_of_continuousOn_time hu))
  have hwi : IntervalIntegrable w volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hw.integrable (by norm_num))
  have hqi : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hq.integrable (by norm_num))
  have hzero := moving_operator_compatibility hT K (fun t => -B t) hK hKd
    w q hwi hqi u₀ (J.adjoint (J w₀)) hcompat (by
      filter_upwards with t
      rw [← hui t]
      simp only [q, neg_apply]
      abel)
  constructor
  · intro t ht
    rw [hWi t ht, hui t]
    exact hzero t ht
  · have hJu (t : ℝ) (ht : t ∈ Icc 0 T) :
        J (u t) = volterraPath (J u₀) W t := by
      have hwit : IntervalIntegrable w volume 0 t := hwi.mono_set (by
        simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl ht.2)
      rw [hui t, map_add, ← J.intervalIntegral_comp_comm hwit]
      congr 1
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le ht.1]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Ioc_subset_Ioc le_rfl ht.2) hgraph] with s hs
      exact hs
    intro t ht
    exact (hasDerivWithinAt_volterraPath_Icc hW ht).congr_of_mem hJu ht

end PoincareConjecture.M35.Uniqueness.Heat
