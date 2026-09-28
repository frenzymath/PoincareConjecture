import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalSegment









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem memLp_continuous_operator {T : ℝ}
    (A : ℝ → V →L[ℝ] H) (hA : ContinuousOn A (Icc 0 T))
    {v : ℝ → V} (hv : MemLp v 2 (timeMeasure T)) :
    MemLp (fun t => A t (v t)) 2 (timeMeasure T) := by
  obtain ⟨C, _, hC⟩ := (isCompact_Icc.image_of_continuousOn hA).isBounded.exists_pos_norm_le
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] H) := ⟨Or.inl inferInstance⟩
  have hm : AEStronglyMeasurable A (timeMeasure T) :=
    (hA.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC _ ⟨t, Ioc_subset_Icc_self ht, rfl⟩
  exact memLp_timeDependent_fun hm hb hv

variable [CompleteSpace V] [CompleteSpace H]

theorem tested_integral_adjoint (I : V →L[ℝ] H) {T : ℝ}
    {D : ℝ → V} (hD : MemLp D 2 (timeMeasure T)) {U : ℝ → H} {u₀ : H}
    (heq : ∀ t ∈ Icc 0 T, ∀ w : V, inner ℝ (I w) (U t) = inner ℝ (I w) u₀ +
      ∫ s in (0 : ℝ)..t, inner ℝ w (D s)) :
    ∀ t ∈ Icc 0 T, I.adjoint (U t) = I.adjoint u₀ + ∫ s in (0 : ℝ)..t, D s := by
  intro t ht
  have hDi : IntervalIntegrable D volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      ((show IntegrableOn D (Ioc 0 T) volume from hD.integrable (by norm_num)).mono_set
        (Ioc_subset_Ioc le_rfl ht.2))
  apply ext_inner_left ℝ
  intro w
  rw [inner_add_right, I.adjoint_inner_right, I.adjoint_inner_right, heq t ht w]
  congr 1
  exact (innerSL ℝ w).intervalIntegral_comp_comm hDi

theorem tested_integral_hasDeriv (I : V →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T)
    {D : ℝ → V} (hD : MemLp D 2 (timeMeasure T)) {U : ℝ → H} {u₀ : H}
    (heq : ∀ t ∈ Icc 0 T, ∀ w : V, inner ℝ (I w) (U t) = inner ℝ (I w) u₀ +
      ∫ s in (0 : ℝ)..t, inner ℝ w (D s)) :
    ∀ᵐ t ∂timeMeasure T, ∀ w : V,
      HasDerivWithinAt (fun s => inner ℝ (I w) (U s)) (inner ℝ w (D t)) (Icc 0 T) t := by
  have hUi := tested_integral_adjoint I hD heq
  have hDi : IntervalIntegrable D volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hD.integrable (by norm_num))
  filter_upwards [ae_restrict_of_ae hDi.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioc] with t ht htime
  have ht' : t ∈ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact Ioc_subset_Icc_self htime
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by simp [hT]
  have hdU : HasDerivAt (fun s => I.adjoint u₀ + ∫ z in (0 : ℝ)..s, D z)
      (D t) t := (ht ht' 0 h0).const_add _
  intro w
  have hp : ∀ s ∈ Icc (0 : ℝ) T, inner ℝ (I w) (U s) =
      inner ℝ w (I.adjoint u₀ + ∫ z in (0 : ℝ)..s, D z) := by
    intro s hs
    rw [← hUi s hs, I.adjoint_inner_right]
  exact (((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hdU).hasDerivWithinAt).congr_of_mem
    hp (Ioc_subset_Icc_self htime)

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
