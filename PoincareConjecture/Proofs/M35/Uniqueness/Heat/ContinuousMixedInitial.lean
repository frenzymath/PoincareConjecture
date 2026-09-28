import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NonautonomousMixedInitial
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalContinuousHeat










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

theorem exists_continuous_mixed_initial_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {b : ℝ} (hb : 0 < b)
    (R : ℝ → V →L[ℝ] V) (hRc : ContinuousOn R (Icc 0 b)) (hR0 : R 0 = 0)
    (L : ℝ → V →L[ℝ] H) (hLc : ContinuousOn L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ v₀ : V,
      ∃ (v : ℝ → V) (U : ℝ → H),
        MemLp v 2 (timeMeasure T) ∧ U 0 = J v₀ ∧ ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : V,
          HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
            (inner ℝ w (R t (v t)) + inner ℝ (J w) (L t (v t)) -
              (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t) := by
  obtain ⟨C, hC, hCb⟩ := (isCompact_Icc.image_of_continuousOn hLc).isBounded.exists_pos_norm_le
  let q : ℝ → ℝ := fun t => ‖R t‖ + Real.sqrt t * (C + 1)
  have hqc : ContinuousOn q (Icc 0 b) :=
    hRc.norm.add ((Real.continuous_sqrt.continuousOn).mul continuousOn_const)
  have hq0 : q 0 = 0 := by simp only [q, hR0, norm_zero, Real.sqrt_zero, zero_mul, add_zero]
  obtain ⟨T, hT, hT1, hTb, hsmall⟩ := exists_small_initial_interval q hb
    (show (0 : ℝ) < 1 / 8 by norm_num) hqc
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖R t‖ + Real.sqrt t * (C + 1) ≤ 1 / 8 := by
    have h := hsmall t ht
    rw [hq0, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self (q t)).trans h
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) : ‖R t‖ ≤ 1 / 8 := by
    have hnq : 0 ≤ Real.sqrt t * (C + 1) := by positivity
    linarith only [hpoint t ht, hnq]
  have hroot : Real.sqrt T ≤ 1 := by
    nlinarith only [Real.sq_sqrt hT.le, Real.sqrt_nonneg T, hT1]
  have hs : (T + 1) * (1 / 8) + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1 := by
    have hq := hpoint T ⟨hT.le, le_rfl⟩
    have hmul := mul_le_mul_of_nonneg_right (show Real.sqrt T + 1 ≤ 2 by linarith)
      (mul_nonneg (Real.sqrt_nonneg T) hC.le)
    nlinarith only [hq, norm_nonneg (R T), Real.sqrt_nonneg T, hT1, hmul]
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 b := fun _ ht => ⟨ht.1, ht.2.trans hTb.le⟩
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] H) := ⟨Or.inl inferInstance⟩
  have hRm : AEStronglyMeasurable R (timeMeasure T) :=
    ((hRc.mono hsub).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hLm : AEStronglyMeasurable L (timeMeasure T) :=
    ((hLc.mono hsub).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hRa : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ 1 / 8 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hRbound t (Ioc_subset_Icc_self ht)
  have hLa : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hCb _ ⟨t, hsub (Ioc_subset_Icc_self ht), rfl⟩
  exact ⟨T, hT, hT1, hTb, fun v₀ =>
    exists_nonautonomous_mixed_initial_heat J hc hd hi hn hT.le (by norm_num)
      hC.le R hRm hRa L hLm hLa hs v₀⟩

end PoincareConjecture.M35.Uniqueness.Heat
