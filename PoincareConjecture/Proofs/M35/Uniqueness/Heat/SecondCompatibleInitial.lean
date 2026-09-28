import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondCompatibleHeat










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

theorem exists_second_compatible_initial_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {b : ℝ} (hb : 0 < b)
    (R : ℝ → V →L[ℝ] V) (hR : ContDiffOn ℝ 1 R (Icc 0 b)) (hR0 : R 0 = 0)
    (L : ℝ → V →L[ℝ] H) (hL : ContDiffOn ℝ 1 L (Icc 0 b))
    (K₁ K₂ : ℝ → V →L[ℝ] V)
    (hK₁ : ContDiffOn ℝ 1 K₁ (Icc 0 b)) (hK₂ : ContinuousOn K₂ (Icc 0 b))
    (hKd : ∀ t ∈ Ioo 0 b,
      HasDerivAt (fun s => mixedHeatOperator J (R s) (L s)) (K₁ t) t)
    (hK₁d : ∀ t ∈ Ioo 0 b, HasDerivAt K₁ (K₂ t) t) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ u₀ w₀ z₀ : V,
      J.adjoint (J w₀) + mixedHeatOperator J (R 0) (L 0) u₀ = 0 →
      J.adjoint (J z₀) + mixedHeatOperator J (R 0) (L 0) w₀ + K₁ 0 u₀ = 0 →
      ∃ (u w : ℝ → V) (Z : ℝ → H), u 0 = u₀ ∧ w 0 = w₀ ∧ Z 0 = J z₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => J (w s)) (Z t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, J.adjoint (J (w t)) +
          mixedHeatOperator J (R t) (L t) (u t) = 0) ∧
        ∀ t ∈ Icc 0 T, J.adjoint (Z t) +
          mixedHeatOperator J (R t) (L t) (w t) + K₁ t (u t) = 0 := by
  have hK : ContDiffOn ℝ 1 (fun t => mixedHeatOperator J (R t) (L t)) (Icc 0 b) :=
    ((contDiffOn_const.sub contDiffOn_const).sub hR).sub
      (contDiffOn_const.clm_comp hL)
  let B : ℝ → V →L[ℝ] V := fun t => -K₁ t - K₁ t
  let N : ℝ → V →L[ℝ] V := fun t => -K₂ t
  have hB : ContinuousOn B (Icc 0 b) := hK₁.continuousOn.neg.sub hK₁.continuousOn
  have hN : ContinuousOn N (Icc 0 b) := hK₂.neg
  obtain ⟨C, hC, hCb⟩ :=
    (isCompact_Icc.image_of_continuousOn hL.continuousOn).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hDb⟩ :=
    (isCompact_Icc.image_of_continuousOn hB).isBounded.exists_pos_norm_le
  obtain ⟨E, hE, hEb⟩ :=
    (isCompact_Icc.image_of_continuousOn hN).isBounded.exists_pos_norm_le
  let q : ℝ → ℝ := fun t => ‖R t‖ + Real.sqrt t * (C + D + E + 1)
  have hqc : ContinuousOn q (Icc 0 b) :=
    hR.continuousOn.norm.add (Real.continuous_sqrt.continuousOn.mul continuousOn_const)
  have hq0 : q 0 = 0 := by simp only [q, hR0, norm_zero, Real.sqrt_zero, zero_mul, add_zero]
  obtain ⟨T, hT, hT1, hTb, hsmall⟩ := exists_small_initial_interval q hb
    (show (0 : ℝ) < 1 / 8 by norm_num) hqc
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖R t‖ + Real.sqrt t * (C + D + E + 1) ≤ 1 / 8 := by
    have h := hsmall t ht
    rw [hq0, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self (q t)).trans h
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) : ‖R t‖ ≤ 1 / 8 := by
    have hp : 0 ≤ Real.sqrt t * (C + D + E + 1) := by positivity
    linarith only [hpoint t ht, hp]
  have hroot : Real.sqrt T ≤ 1 := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hT1]
  have hTr : T ≤ Real.sqrt T := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hroot]
  have hqT := hpoint T ⟨hT.le, le_rfl⟩
  have hsC : Real.sqrt T * C ≤ 1 / 8 := by
    nlinarith only [hqT, norm_nonneg (R T), Real.sqrt_nonneg T, hD.le, hE.le]
  have hsDE : Real.sqrt T * (D + E) ≤ 1 / 8 := by
    nlinarith only [hqT, norm_nonneg (R T), Real.sqrt_nonneg T, hC.le]
  have hTTr : T * T ≤ Real.sqrt T :=
    (mul_le_of_le_one_right hT.le hT1).trans hTr
  have hDET : D * T + E * (T * T) ≤ 1 / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hTr hD.le
    have h2 := mul_le_mul_of_nonneg_left hTTr hE.le
    nlinarith only [h1, h2, hsDE]
  have hs : (T + 1) * (1 / 8 + D * T + E * (T * T)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * C < 1 := by
    have hp := mul_le_mul (by linarith only [hT1] : T + 1 ≤ 2)
      (by linarith only [hDET] : 1 / 8 + D * T + E * (T * T) ≤ 1 / 4)
      (by positivity : 0 ≤ 1 / 8 + D * T + E * (T * T)) (by norm_num : (0 : ℝ) ≤ 2)
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
  have hRa : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ 1 / 8 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hRbound t (Ioc_subset_Icc_self ht)
  have hLa : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hCb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  have hBa : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hDb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  have hNa : ∀ᵐ t ∂timeMeasure T, ‖N t‖ ≤ E := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hEb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ z₀ hcompat hcompat₁
  exact exists_second_compatible_heat J hc hd hi hn hT.le (by norm_num) hC.le hD.le hE.le
    R hRm hRa L hLm hLa K₁ K₂ (hK.mono hsub) (hK₁.mono hsub) (hK₂.mono hsub)
    (fun t ht => hKd t ⟨ht.1, ht.2.trans hTb⟩)
    (fun t ht => hK₁d t ⟨ht.1, ht.2.trans hTb⟩) hBa hNa hs u₀ w₀ z₀ hcompat hcompat₁

end PoincareConjecture.M35.Uniqueness.Heat
