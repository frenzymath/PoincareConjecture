import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousMixedInitial










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

def mixedHeatOperator (J : V →L[ℝ] H) (R : V →L[ℝ] V) (L : V →L[ℝ] H) :
    V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - J.adjoint.comp J - R - J.adjoint.comp L

theorem exists_strong_mixed_initial_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {b : ℝ} (hb : 0 < b)
    (R : ℝ → V →L[ℝ] V) (hR : ContDiffOn ℝ 1 R (Icc 0 b)) (hR0 : R 0 = 0)
    (L : ℝ → V →L[ℝ] H) (hL : ContDiffOn ℝ 1 L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ u₀ w₀ : V,
      J.adjoint (J w₀) + mixedHeatOperator J (R 0) (L 0) u₀ = 0 →
      ∃ (u : ℝ → V) (W : ℝ → H), u 0 = u₀ ∧ W 0 = J w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn W (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => J (u s)) (W t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, J.adjoint (W t) + mixedHeatOperator J (R t) (L t) (u t) = 0) ∧
        ∃ w : ℝ → V, MemLp w 2 (timeMeasure T) ∧
          ∀ᵐ t ∂timeMeasure T, HasDerivAt u (w t) t ∧ J (w t) = W t := by
  let K : ℝ → V →L[ℝ] V := fun t => mixedHeatOperator J (R t) (L t)
  have hK : ContDiffOn ℝ 1 K (Icc 0 b) :=
    ((contDiffOn_const.sub contDiffOn_const).sub hR).sub
      (contDiffOn_const.clm_comp hL)
  let B : ℝ → V →L[ℝ] V := fun t => -derivWithin K (Icc 0 b) t
  have hB : ContinuousOn B (Icc 0 b) :=
    (hK.continuousOn_derivWithin (uniqueDiffOn_Icc hb) le_rfl).neg
  obtain ⟨C, hC, hCb⟩ :=
    (isCompact_Icc.image_of_continuousOn hL.continuousOn).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hDb⟩ :=
    (isCompact_Icc.image_of_continuousOn hB).isBounded.exists_pos_norm_le
  let q : ℝ → ℝ := fun t => ‖R t‖ + Real.sqrt t * (C + D + 1)
  have hqc : ContinuousOn q (Icc 0 b) :=
    hR.continuousOn.norm.add (Real.continuous_sqrt.continuousOn.mul continuousOn_const)
  have hq0 : q 0 = 0 := by simp only [q, hR0, norm_zero, Real.sqrt_zero, zero_mul, add_zero]
  obtain ⟨T, hT, hT1, hTb, hsmall⟩ := exists_small_initial_interval q hb
    (show (0 : ℝ) < 1 / 8 by norm_num) hqc
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖R t‖ + Real.sqrt t * (C + D + 1) ≤ 1 / 8 := by
    have h := hsmall t ht
    rw [hq0, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self (q t)).trans h
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) : ‖R t‖ ≤ 1 / 8 := by
    have hp : 0 ≤ Real.sqrt t * (C + D + 1) := by positivity
    linarith only [hpoint t ht, hp]
  have hroot : Real.sqrt T ≤ 1 := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hT1]
  have hTr : T ≤ Real.sqrt T := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hroot]
  have hqT := hpoint T ⟨hT.le, le_rfl⟩
  have hsC : Real.sqrt T * C ≤ 1 / 8 := by
    nlinarith only [hqT, norm_nonneg (R T), Real.sqrt_nonneg T, hD.le]
  have hsD : Real.sqrt T * D ≤ 1 / 8 := by
    nlinarith only [hqT, norm_nonneg (R T), Real.sqrt_nonneg T, hC.le]
  have hDT : D * T ≤ 1 / 8 := by
    nlinarith only [mul_le_mul_of_nonneg_left hTr hD.le, hsD]
  have hs : (T + 1) * (1 / 8 + D * T) +
      (Real.sqrt T * (Real.sqrt T + 1)) * C < 1 := by
    have hp := mul_le_mul (by linarith only [hT1] : T + 1 ≤ 2)
      (by linarith only [hDT] : 1 / 8 + D * T ≤ 1 / 4)
      (by positivity : 0 ≤ 1 / 8 + D * T) (by norm_num : (0 : ℝ) ≤ 2)
    have hq := mul_le_mul_of_nonneg_left (show Real.sqrt T + 1 ≤ 2 by linarith)
      (mul_nonneg (Real.sqrt_nonneg T) hC.le)
    nlinarith only [hp, hq, hsC]
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 b := fun _ ht => ⟨ht.1, ht.2.trans hTb.le⟩
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] H) := ⟨Or.inl inferInstance⟩
  have hRm : AEStronglyMeasurable R (timeMeasure T) :=
    ((hR.continuousOn.mono hsub).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hLm : AEStronglyMeasurable L (timeMeasure T) :=
    ((hL.continuousOn.mono hsub).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hBm : AEStronglyMeasurable B (timeMeasure T) :=
    ((hB.mono hsub).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hRa : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ 1 / 8 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hRbound t (Ioc_subset_Icc_self ht)
  have hLa : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hCb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  have hBa : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hDb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  have hKd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt K (-B t) t := by
    have htb : t < b := ht.2.trans hTb
    have hd := ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hb)).mp hK).1
      t ⟨ht.1.le, htb.le⟩
    simpa only [B, neg_neg] using hd.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 htb)
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ hcompat
  obtain ⟨u, w, W, hw, hu0, hW0, hu, hW, hgraph, hui, hdu, hWi⟩ :=
    exists_differentiated_form_heat J hc hd hi hn hT.le (by norm_num) hC.le hD.le
      R hRm hRa L hLm hLa B hBm hBa hs u₀ w₀
  have hWi' (t : ℝ) (ht : t ∈ Icc 0 T) :
      J.adjoint (W t) = J.adjoint (J w₀) +
        ∫ s in (0 : ℝ)..t, -K s (w s) + B s (u s) := by
    rw [hWi t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only [K, mixedHeatOperator, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply]
    abel
  have hrec := strong_heat_recovery J hT.le K B (hK.mono hsub) (hB.mono hsub) hKd
    u w W u₀ w₀ hw hu hW hgraph hui hWi' hcompat
  refine ⟨u, W, hu0, hW0, hu, hW, hrec.2, hrec.1, w, hw, ?_⟩
  filter_upwards [hdu, hgraph] with t ht hg
  exact ⟨ht, hg⟩

end PoincareConjecture.M35.Uniqueness.Heat
