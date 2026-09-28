








import PoincareConjecture.Proofs.M07.Analysis.ODE.LocalFlow.HigherRegularity.VariationalOrbitComparison


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace Poincare.ODE.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] variationalAugmentedEndNormedAddCommGroup

section LevelOneSmoothnessClause

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E}

theorem exists_isLocalFlow_augmentedVectorField_and_contDiffOn_fromAugFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (R_aug : ℝ≥0) (ε_aug : ℝ) (_hR_aug : 0 < R_aug) (_hε_aug : 0 < ε_aug)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
      (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ)),
      IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
          (t₀ - ε_aug) (t₀ + ε_aug) aΦ ∧
        ContDiffOn ℝ 1 (fromAugFlow aΦ)
          ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, haΦ⟩ :=
    exists_isLocalFlow_augVF_of_C2 hf_C2 t₀ p₀
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  set R_a_out : ℝ := (R_aug : ℝ) / 2 with hR_a_out_def
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by exact_mod_cast hR_aug_pos
  have hR_a_out_pos : 0 < R_a_out := by rw [hR_a_out_def]; linarith
  have hR_a_out_lt : R_a_out < (R_aug : ℝ) := by rw [hR_a_out_def]; linarith
  set T_a_out : ℝ := ε_aug / 2 with hT_a_out_def
  have hT_a_out_pos : 0 < T_a_out := by rw [hT_a_out_def]; linarith
  have hT_a_out_lt : T_a_out < ε_aug := by rw [hT_a_out_def]; linarith
  have hslab_sub_a : closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)
      ⊆ closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug) := by
    refine Set.prod_mono ?_ ?_
    · exact closedBall_subset_closedBall (le_of_lt hR_a_out_lt)
    · exact Icc_subset_Icc (by linarith) (by linarith)
  have hpartial_a : ContDiffOn ℝ 0 (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    contDiffOn_partial_fderiv_of_succ (f := augmentedVectorField f) (k := (0 : ℕ∞))
      (by simpa using h_augVF_C1)
  have hpartial_a_cont : ContinuousOn (fun p : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (augmentedVectorField f p.1) p.2) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hpartial_a.continuousOn
  have haΦ_cont_full : ContinuousOn aΦ
      (closedBall p₀ (R_aug : ℝ) ×ˢ Icc (t₀ - ε_aug) (t₀ + ε_aug)) :=
    haΦ.continuousOn
  have haΦ_cont : ContinuousOn aΦ
      (closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out)) :=
    haΦ_cont_full.mono hslab_sub_a
  set Slab : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    closedBall p₀ R_a_out ×ˢ Icc (t₀ - T_a_out) (t₀ + T_a_out) with hSlab_def
  have hSlab_cpt : IsCompact Slab :=
    (isCompact_closedBall (p₀ : E × (E →L[ℝ] E)) R_a_out).prod isCompact_Icc
  have hSlab_ne : Slab.Nonempty :=
    ⟨(p₀, t₀), Metric.mem_closedBall_self (le_of_lt hR_a_out_pos),
      ⟨by linarith, by linarith⟩⟩
  have h_aΦ_pair_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q)) Slab :=
    ContinuousOn.prodMk continuous_snd.continuousOn haΦ_cont
  have h_fderiv_along_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => fderiv ℝ (augmentedVectorField f q.2) (aΦ q))
      Slab := by
    have hmaps : MapsTo (fun q : (E × (E →L[ℝ] E)) × ℝ => (q.2, aΦ q))
        Slab (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := fun _ _ => mem_univ _
    exact hpartial_a_cont.comp h_aΦ_pair_cont hmaps
  have h_norm_cont : ContinuousOn
      (fun q : (E × (E →L[ℝ] E)) × ℝ => ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖)
      Slab := by
    have hnorm : Continuous
        (fun A : (E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E)) => ‖A‖) :=
      continuous_norm
    exact hnorm.comp_continuousOn h_fderiv_along_cont
  rcases hSlab_cpt.exists_isMaxOn hSlab_ne h_norm_cont with ⟨qmax, _, hqmax⟩
  set M_aug_pre : ℝ := ‖fderiv ℝ (augmentedVectorField f qmax.2) (aΦ qmax)‖ with hM_aug_pre_def
  have hM_aug_pre_nn : 0 ≤ M_aug_pre := norm_nonneg _
  have hM_aug_pre_bd : ∀ q ∈ Slab, ‖fderiv ℝ (augmentedVectorField f q.2) (aΦ q)‖ ≤ M_aug_pre :=
    fun q hq => hqmax hq
  set M_aug : ℝ := M_aug_pre + 1 with hM_aug_def
  have hM_aug_nn : 0 ≤ M_aug := by rw [hM_aug_def]; linarith
  have hM_aug_pos : 0 < M_aug := by rw [hM_aug_def]; linarith
  set T_a_mid' : ℝ := min (T_a_out * 3 / 4) (1 / (2 * M_aug)) with hT_a_mid'_def
  have hT_a_mid'_pos : 0 < T_a_mid' := by
    refine lt_min ?_ ?_
    · positivity
    · have : 0 < 2 * M_aug := by linarith
      positivity
  have hT_a_mid'_lt_out : T_a_mid' < T_a_out := by
    have h1 : T_a_mid' ≤ T_a_out * 3 / 4 := min_le_left _ _
    have h2 : T_a_out * 3 / 4 < T_a_out := by linarith
    linarith
  have hMTmid' : M_aug * T_a_mid' < 1 := by
    have h1 : T_a_mid' ≤ 1 / (2 * M_aug) := min_le_right _ _
    have h2 : M_aug * T_a_mid' ≤ M_aug * (1 / (2 * M_aug)) :=
      mul_le_mul_of_nonneg_left h1 hM_aug_nn
    have h3 : M_aug * (1 / (2 * M_aug)) = 1 / 2 := by field_simp
    linarith
  set T_a : ℝ := T_a_mid' / 2 with hT_a_def
  have hT_a_pos : 0 < T_a := by rw [hT_a_def]; linarith
  have hT_a_lt_mid' : T_a < T_a_mid' := by rw [hT_a_def]; linarith
  set R_a_mid : ℝ := R_a_out * 3 / 4 with hR_a_mid_def
  have hR_a_mid_pos : 0 < R_a_mid := by rw [hR_a_mid_def]; positivity
  have hR_a_mid_lt_out : R_a_mid < R_a_out := by rw [hR_a_mid_def]; linarith
  set R_a : ℝ := R_a_mid / 2 with hR_a_def
  have hR_a_pos : 0 < R_a := by rw [hR_a_def]; linarith
  have hR_a_lt_mid : R_a < R_a_mid := by rw [hR_a_def]; linarith
  set R_aN : ℝ≥0 := ⟨R_a, le_of_lt hR_a_pos⟩ with hR_aN_def
  set R_a_midN : ℝ≥0 := ⟨R_a_mid, le_of_lt hR_a_mid_pos⟩ with hR_a_midN_def
  set R_a_outN : ℝ≥0 := ⟨R_a_out, le_of_lt hR_a_out_pos⟩ with hR_a_outN_def
  set r'a : ℝ≥0 := ⟨R_aug / 8, by positivity⟩ with hr'a_def
  have hr'a_pos : (0 : ℝ) < (r'a : ℝ) := by
    rw [hr'a_def]
    change 0 < (R_aug : ℝ) / 8
    linarith
  have hR_a_outN_eq : (R_a_outN : ℝ) = R_a_out := rfl
  have hR_a_midN_eq : (R_a_midN : ℝ) = R_a_mid := rfl
  have hR_aN_eq : (R_aN : ℝ) = R_a := rfl
  have hρρ_aux : (R_a_midN : ℝ) + (r'a : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_midN_eq, hR_a_mid_def, hR_a_out_def]
    have : (r'a : ℝ) = (R_aug : ℝ) / 8 := rfl
    linarith
  have hR_a_out_le_R_aug : (R_a_outN : ℝ) ≤ (R_aug : ℝ) := by
    rw [hR_a_outN_eq, hR_a_out_def]; linarith
  have hA_bd_a : ∀ p ∈ closedBall p₀ (R_a_outN : ℝ),
      ∀ τ ∈ Icc (t₀ - T_a_out) (t₀ + T_a_out),
        ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug := by
    intro p hp τ hτ
    have hq_in : ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) ∈ Slab := ⟨hp, hτ⟩
    have h_pre : ‖fderiv ℝ (augmentedVectorField f τ) (aΦ ⟨p, τ⟩)‖ ≤ M_aug_pre :=
      hM_aug_pre_bd ((p, τ) : (E × (E →L[ℝ] E)) × ℝ) hq_in
    exact h_pre.trans (le_add_of_nonneg_right zero_le_one)
  have hsub_a : Icc (t₀ - T_a_out) (t₀ + T_a_out) ⊆ Icc (t₀ - ε_aug) (t₀ + ε_aug) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have h_aug_C1 : ContDiffOn ℝ 1 aΦ ((ball p₀ (R_aN : ℝ))
      ×ˢ Ioo (t₀ - T_a) (t₀ + T_a)) := by
    have hk_aug : (1 : ℕ∞) ≤ 1 := le_refl _
    refine contDiffOn_flow_of_isLocalFlow_of_contDiff (f := augmentedVectorField f)
      (t₀ := t₀) (x₀ := p₀) (r := R_aug) (tmin := t₀ - ε_aug) (tmax := t₀ + ε_aug)
      (Φ := aΦ) haΦ hk_aug h_augVF_C1 hT_a_pos hT_a_lt_mid' hT_a_mid'_lt_out
      hM_aug_nn hMTmid' hsub_a (ρ_out := R_a_outN) (ρ_mid := R_a_midN) (ρ := R_aN)
      hr'a_pos
      ?_ ?_ ?_ ?_ hA_bd_a
    · rw [hR_aN_eq, hR_a_midN_eq]; linarith [hR_a_lt_mid]
    · rw [hR_a_midN_eq, hR_a_outN_eq]; linarith [hR_a_mid_lt_out]
    · exact hρρ_aux
    · exact hR_a_out_le_R_aug
  set T : ℝ := T_a / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_le_T_a : T ≤ T_a := by rw [hT_def]; linarith
  set ρ : ℝ := R_a / 2 with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
  have hρ_le_R_a : ρ ≤ R_a := by rw [hρ_def]; linarith
  set ρN : ℝ≥0 := ⟨ρ, le_of_lt hρ_pos⟩ with hρN_def
  have hρN_eq : (ρN : ℝ) = ρ := rfl
  have hρN_le_R_aN : (ρN : ℝ) ≤ (R_aN : ℝ) := by rw [hρN_eq, hR_aN_eq]; exact hρ_le_R_a
  refine ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, T, ρN, hT_pos, hρ_pos, haΦ, ?_⟩
  exact contDiffOn_fromAugFlow_inherits (ρ_a := R_aN) (ρ := ρN) (T_a := T_a) (T := T)
    hρN_le_R_aN hT_le_T_a h_aug_C1

theorem exists_contDiffOn_fromAugFlow_one_of_C2
    [FiniteDimensional ℝ E]
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (x₀ : E) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      ContDiffOn ℝ 1 (fromAugFlow aΦ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  obtain ⟨_, _, _, _, aΦ, T, ρ, hT, hρ, _, h_smooth⟩ :=
    exists_isLocalFlow_augmentedVectorField_and_contDiffOn_fromAugFlow_one_of_C2
      hf_C2 t₀ x₀
  exact ⟨T, ρ, hT, hρ, aΦ, h_smooth⟩

end LevelOneSmoothnessClause

end Poincare.ODE.LocalFlow

end
