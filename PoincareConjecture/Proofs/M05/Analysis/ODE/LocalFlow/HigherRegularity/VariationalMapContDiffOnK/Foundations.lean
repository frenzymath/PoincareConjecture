import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.HigherRegularity.ContDiffOnK

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace Poincare.ODE.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section AugVFDefinition

def augmentedVectorField (f : ℝ → E → E) : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E)) :=
  fun t p => (f t p.1, ((fderiv ℝ (f t) p.1).comp p.2))

omit [CompleteSpace E] in
@[simp]
lemma augVF_apply (f : ℝ → E → E) (t : ℝ) (x : E) (Z : E →L[ℝ] E) :
    augmentedVectorField f t (x, Z) = (f t x, ((fderiv ℝ (f t) x).comp Z)) := rfl

end AugVFDefinition

section PartialFDerivSmoothness

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
lemma partial_fderiv_eq_comp_inr_on_univ
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∀ p : ℝ × E, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p := by
    have hp_open : (Set.univ : Set (ℝ × E)) ∈ 𝓝 p := isOpen_univ.mem_nhds (mem_univ _)
    exact (hf.contDiffAt hp_open).differentiableAt one_ne_zero
  exact fderiv_eq_comp_inr hdiff_joint

omit [CompleteSpace E] in
theorem contDiffOn_partial_fderiv_of_succ
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)) := by
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) := by
    have h : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) :=
      hf_succ.fderiv_of_isOpen isOpen_univ le_rfl
    exact h
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    rfl
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) (Set.univ : Set (ℝ × E)) :=
    hfderiv_Ck.continuousLinearMap_comp postL
  have heq : ∀ p ∈ (Set.univ : Set (ℝ × E)),
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p _
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast h1
      have := hf_succ.of_le h1'
      simpa using this
    have h := partial_fderiv_eq_comp_inr_on_univ hf_C1 p
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

omit [CompleteSpace E] in
lemma partial_fderiv_eq_comp_inr_on_open
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 (uncurry f) Ω) :
    ∀ p ∈ Ω, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p hp
  have hp_open : Ω ∈ 𝓝 p := hΩ.mem_nhds hp
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p :=
    ((hf.contDiffAt hp_open).differentiableAt one_ne_zero)
  exact fderiv_eq_comp_inr hdiff_joint

omit [CompleteSpace E] in
theorem contDiffOn_partial_fderiv_of_succ_local
    {k : ℕ∞} {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) Ω) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Ω := by
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) Ω :=
    hf_succ.fderiv_of_isOpen hΩ le_rfl
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    rfl
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) Ω :=
    hfderiv_Ck.continuousLinearMap_comp postL
  have heq : ∀ p ∈ Ω,
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p hp
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast h1
      exact hf_succ.of_le h1'
    have h := partial_fderiv_eq_comp_inr_on_open hΩ hf_C1 p hp
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

end PartialFDerivSmoothness

section AugVFSmoothness

variable {f : ℝ → E → E}

omit [CompleteSpace E] in
theorem augVF_uncurry_contDiff
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  set proj1 : ℝ × (E × (E →L[ℝ] E)) → ℝ × E := fun q => (q.1, q.2.1) with hproj1_def
  have hproj1_Ck : ContDiffOn ℝ k proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact contDiff_fst.contDiffOn
    · exact (contDiff_fst.comp contDiff_snd).contDiffOn
  have hmaps1 : MapsTo proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_succ.of_le h_le
  have hcomp1 : ContDiffOn ℝ k (uncurry f ∘ proj1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hf_Ck.comp hproj1_Ck hmaps1
  have heq1 : (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1) = uncurry f ∘ proj1 := by
    funext q; rfl
  have hC1 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq1]; exact hcomp1
  have hpartial_Ck := contDiffOn_partial_fderiv_of_succ hf_succ
  have hA_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (f q.1) q.2.1) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have hcomp := hpartial_Ck.comp hproj1_Ck hmaps1
    have heq : (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) ∘ proj1
        = (fun q : ℝ × (E × (E →L[ℝ] E)) => fderiv ℝ (f q.1) q.2.1) := by
      funext q; rfl
    rw [← heq]; exact hcomp
  have hZ_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hpair_Ck : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hA_Ck.prodMk hZ_Ck
  have hbilin_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).contDiff
  have hbilin_Ck : ContDiffOn ℝ k
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2)
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := hbilin_smooth.contDiffOn
  have hmaps_pair : MapsTo (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hC2_pre : ContDiffOn ℝ k
      ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
       (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hbilin_Ck.comp hpair_Ck hmaps_pair
  have heq2 : ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
        (fun q : ℝ × (E × (E →L[ℝ] E)) =>
         ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      = (fun q : ℝ × (E × (E →L[ℝ] E)) =>
          (fderiv ℝ (f q.1) q.2.1).comp q.2.2) := by
    funext q; rfl
  have hC2 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (fderiv ℝ (f q.1) q.2.1).comp q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq2] at hC2_pre; exact hC2_pre
  have hpair_final : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hC1.prodMk hC2
  have heq_final : (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      = uncurry (augmentedVectorField f) := by
    funext q; rfl
  rw [heq_final] at hpair_final
  exact hpair_final

omit [CompleteSpace E] in
theorem augVF_uncurry_continuousOn_of_C1
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContinuousOn (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  have hf_succ : ContDiffOn ℝ ((0 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C1
  have h := augVF_uncurry_contDiff (k := (0 : ℕ∞)) hf_succ
  exact contDiffOn_zero.mp h

end AugVFSmoothness

section NestingData

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem continuousOn_fderiv_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ : ρ ≤ (r : ℝ)) :
    ContinuousOn (fun p : E × ℝ => fderiv ℝ (f p.2) (Φ p))
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have hΦcont : ContinuousOn Φ ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    hΦ.continuousOn.mono (Set.prod_mono (closedBall_subset_closedBall hρ) (le_refl _))
  have hmap : ContinuousOn (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) :=
    (continuousOn_snd).prodMk hΦcont
  have hmaps : MapsTo (fun p : E × ℝ => (p.2, Φ p))
      ((closedBall x₀ ρ) ×ˢ Icc tmin tmax) (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  exact hpartial.comp hmap hmaps

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem exists_norm_fderiv_le_along_flow_joint
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ : ρ ≤ (r : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall x₀ ρ, ∀ τ ∈ Icc tmin tmax,
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
  have hcont := continuousOn_fderiv_along_flow_joint hΦ hf hρ
  have hcontN : ContinuousOn (fun p : E × ℝ => ‖fderiv ℝ (f p.2) (Φ p)‖)
      ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) := continuous_norm.comp_continuousOn hcont
  have hcompact : IsCompact ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)) :=
    (isCompact_closedBall x₀ ρ).prod isCompact_Icc
  have hne : ((closedBall x₀ ρ) ×ˢ (Icc tmin tmax)).Nonempty :=
    ⟨(x₀, t₀), ⟨mem_closedBall_self hρ_nonneg, hΦ.t₀_mem_Icc⟩⟩
  obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
  use ‖fderiv ℝ (f p.2) (Φ p)‖, norm_nonneg _
  intro x hx τ hτ
  have hmem : ((x, τ) : E × ℝ) ∈ (closedBall x₀ ρ) ×ˢ (Icc tmin tmax) := ⟨hx, hτ⟩
  exact hp_max hmem

omit [CompleteSpace E] in
theorem exists_lipschitzOnWith_closedBall_of_C1
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (x₀ : E) (ρ : ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (closedBall x₀ ρ) := by
  have hpartial : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Set.univ : Set (ℝ × E)) := by
    have h := continuousOn_partialFDeriv_uncurry (f := f)
      (s := (Set.univ : Set ℝ)) (u := (Set.univ : Set E))
      (by rwa [Set.univ_prod_univ]) isOpen_univ isOpen_univ
    rwa [Set.univ_prod_univ] at h
  have hcontN : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (f p.1) p.2‖)
      ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    (continuous_norm.comp_continuousOn (hpartial.mono (subset_univ _)))
  have hcompact : IsCompact ((Icc a b) ×ˢ (closedBall x₀ ρ)) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ ρ)
  have hdiff : ∀ t : ℝ, ∀ x : E, DifferentiableAt ℝ (f t) x := by
    intro t x
    have hDiff_joint : DifferentiableAt ℝ (uncurry f) (t, x) :=
      (hf.contDiffAt (isOpen_univ.mem_nhds (mem_univ _))).differentiableAt one_ne_zero
    have hg : DifferentiableAt ℝ (fun y : E => (t, y)) x :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact hDiff_joint.comp x hg
  by_cases hball : (closedBall x₀ ρ).Nonempty
  · obtain ⟨x₁, hx₁⟩ := hball
    have hne : ((Icc a b) ×ˢ (closedBall x₀ ρ)).Nonempty := ⟨(a, x₁), ⟨⟨le_rfl, hab⟩, hx₁⟩⟩
    obtain ⟨p, hp, hp_max⟩ := hcompact.exists_isMaxOn hne hcontN
    set C : ℝ := ‖fderiv ℝ (f p.1) p.2‖ with hC_def
    let K : ℝ≥0 := ⟨C, norm_nonneg _⟩
    have hK : ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (closedBall x₀ ρ) := by
      intro t ht
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        (fun x _ => hdiff t x) ?_ (convex_closedBall x₀ ρ)
      intro x hx
      have hmem : ((t, x) : ℝ × E) ∈ (Icc a b) ×ˢ (closedBall x₀ ρ) :=
        Set.mem_prod.mpr ⟨ht, hx⟩
      have : ‖fderiv ℝ (f t) x‖ ≤ C := hp_max hmem
      rw [← NNReal.coe_le_coe]
      change ‖fderiv ℝ (f t) x‖ ≤ C
      exact this
    exact Exists.intro K hK
  · have hK : ∀ t ∈ Icc a b, LipschitzOnWith 0 (f t) (closedBall x₀ ρ) := by
      intro t _
      rw [not_nonempty_iff_eq_empty] at hball
      rw [hball]
      exact lipschitzOnWith_empty 0 (f t)
    exact Exists.intro 0 hK

omit [CompleteSpace E] in
theorem exists_flow_nesting_data
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ (T_out T_mid T M : ℝ) (ρ_out ρ_mid ρ r' : ℝ≥0),
      0 < T ∧ T < T_mid ∧ T_mid < T_out ∧ 0 ≤ M ∧ M * T_mid < 1 ∧ 0 < (r' : ℝ) ∧
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < (ρ_mid : ℝ) ∧ (ρ_mid : ℝ) < (ρ_out : ℝ) ∧
      (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) ∧ (ρ_out : ℝ) ≤ (r : ℝ) ∧
      Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax ∧
      (∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) := by
  let ρ_out : ℝ≥0 := r / 2
  let ρ_mid : ℝ≥0 := r / 4
  let ρ : ℝ≥0 := r / 8
  let r' : ℝ≥0 := r / 2
  have hρ_out_coe : (ρ_out : ℝ) = (r : ℝ) / 2 := by simp only [ρ_out]; push_cast; ring
  have hρ_mid_coe : (ρ_mid : ℝ) = (r : ℝ) / 4 := by simp only [ρ_mid]; push_cast; ring
  have hρ_coe : (ρ : ℝ) = (r : ℝ) / 8 := by simp only [ρ]; push_cast; ring
  have hr'_coe : (r' : ℝ) = (r : ℝ) / 2 := by simp only [r']; push_cast; ring
  have hρ_pos : 0 < (ρ : ℝ) := by rw [hρ_coe]; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by rw [hρ_coe, hρ_mid_coe]; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by rw [hρ_mid_coe, hρ_out_coe]; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by rw [hρ_mid_coe, hr'_coe]; linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ) := by rw [hρ_out_coe]; linarith
  have hr'_pos : 0 < (r' : ℝ) := by rw [hr'_coe]; linarith
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_out : ℝ := d / 2 with hT_out_def
  have hT_out_pos : 0 < T_out := by rw [hT_out_def]; linarith
  have hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have : d ≤ t₀ - tmin := min_le_left _ _
      rw [hT_out_def]; linarith
    · have : d ≤ tmax - t₀ := min_le_right _ _
      rw [hT_out_def]; linarith
  obtain ⟨M, hM_nonneg, hM_bd⟩ :=
    exists_norm_fderiv_le_along_flow_joint hΦ hf (ρ := (ρ_out : ℝ))
      (NNReal.coe_nonneg ρ_out) hρ_out_le_r
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    exact hM_bd x hx τ (hsub hτ)
  set T_mid : ℝ := min (T_out / 2) (1 / (2 * (M + 1))) with hT_mid_def
  have hM1_pos : 0 < 2 * (M + 1) := by linarith
  have hT_mid_pos : 0 < T_mid := lt_min (by linarith) (by positivity)
  have hT_mid_lt_out : T_mid < T_out := by
    calc T_mid ≤ T_out / 2 := min_le_left _ _
      _ < T_out := by linarith
  set T : ℝ := T_mid / 2 with hT_def
  have hT_pos : 0 < T := by rw [hT_def]; linarith
  have hT_lt_mid : T < T_mid := by rw [hT_def]; linarith
  have hMT_mid : M * T_mid < 1 := by
    have hle : T_mid ≤ 1 / (2 * (M + 1)) := min_le_right _ _
    have hM_T_mid : M * T_mid ≤ M * (1 / (2 * (M + 1))) := by
      apply mul_le_mul_of_nonneg_left hle hM_nonneg
    calc M * T_mid ≤ M * (1 / (2 * (M + 1))) := hM_T_mid
      _ = M / (2 * (M + 1)) := by ring
      _ < 1 := by
          rw [div_lt_one hM1_pos]; linarith
  exact ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT_pos, hT_lt_mid, hT_mid_lt_out,
    hM_nonneg, hMT_mid, hr'_pos, hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r,
    hsub, hA_bd⟩

end NestingData

section ProjectionPredicate

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

structure IsVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) (T : ℝ) (ρ : ℝ≥0)
    (Y : E × ℝ → (E →L[ℝ] E)) (k : ℕ∞) : Prop where
  contDiffOn : ContDiffOn ℝ k Y ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))
  fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
    fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q)

omit [CompleteSpace E] in
lemma IsVariationalFlowProjection.of_le {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T : ℝ} {ρ : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k j : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) (hjk : j ≤ k) :
    IsVariationalFlowProjection hΦ T ρ Y j := by
  refine
  { contDiffOn := ?_,
    fderiv_eq := hY.fderiv_eq }
  have hjk' : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
  exact hY.contDiffOn.of_le hjk'

end ProjectionPredicate

section RecursiveFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_succ_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
  contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck
    hY.contDiffOn hY.fderiv_eq

theorem contDiffOn_flow_of_isVariationalFlowProjection_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (Y_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hY_seq : ∀ j : ℕ, j + 1 ≤ k →
      IsVariationalFlowProjection hΦ T ρ (Y_seq j) (j : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  refine contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_ ?_
  · intro j hj
    exact (hY_seq j hj).contDiffOn
  · intro j hj
    exact (hY_seq j hj).fderiv_eq

theorem contDiffOn_flow_of_isVariationalFlowProjection_top
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ) (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y ((k - 1 : ℕ) : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun _ => Y with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  have hj_le : (j : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
    have h : j ≤ k - 1 := by omega
    exact_mod_cast h
  exact hY.of_le hj_le

end RecursiveFlow

section FderivCoprodIdentity

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

def spatialPieceFn (Φ : E × ℝ → E) : E × ℝ → (E →L[ℝ] E) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [CompleteSpace E] in
@[simp]
lemma spatialPieceFn_apply (Φ : E × ℝ → E) (q : E × ℝ) :
    spatialPieceFn Φ q = (fderiv ℝ Φ q).comp (ContinuousLinearMap.inl ℝ E ℝ) := rfl

theorem fderiv_flow_eq_coprod_spatialPiece
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) := by
  have hT_mid_pos : 0 < T_mid := lt_trans hT hT_lt_mid
  have hρ_mid_pos : 0 < (ρ_mid : ℝ) := lt_of_le_of_lt (ρ.coe_nonneg) hρ_lt_mid
  have hsub_mid_out : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_mid : Icc (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin tmax := hsub_mid_out.trans hsub
  have hA_bd_mid : ∀ x ∈ closedBall x₀ (ρ_mid : ℝ), ∀ τ ∈ Icc (t₀ - T_mid) (t₀ + T_mid),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ =>
    hA_bd x (closedBall_subset_closedBall (le_of_lt hρ_mid_lt_out) hx) τ (hsub_mid_out hτ)
  intro q hq
  rcases hq with ⟨hq_x, hq_t⟩
  rw [mem_ball] at hq_x
  obtain ⟨x, t⟩ := q
  have hx_cb_mid : x ∈ closedBall x₀ (ρ_mid : ℝ) :=
    mem_closedBall.mpr (le_of_lt (lt_trans hq_x hρ_lt_mid))
  have hq_t_mid : t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid) :=
    ⟨by linarith [hq_t.1], by linarith [hq_t.2]⟩
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT_mid_pos hM hMT_mid hsub_mid hr' hρρ'
    hA_bd_mid hx_cb_mid hq_t_mid
  have hfd_eq := hfd_at.fderiv
  set Lsp : E →L[ℝ] E :=
    variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀)
      hT_mid_pos hM hMT_mid
      (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
          rw [mem_closedBall] at hx_cb_mid; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
        (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub_mid)
      (fun τ hτ => hA_bd_mid x hx_cb_mid τ hτ) (Ioo_subset_Icc_self hq_t_mid) with hLsp_def
  set Lti : ℝ →L[ℝ] E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f t (Φ ⟨x, t⟩)) with hLti_def
  have hti_eq : timePieceFn f Φ (x, t) = Lti := rfl
  have hsp_eq : spatialPieceFn Φ (x, t) = Lsp := by
    rw [spatialPieceFn_apply, hfd_eq]
    exact ContinuousLinearMap.coprod_comp_inl Lsp Lti
  rw [hsp_eq, hti_eq, hfd_eq]

end FderivCoprodIdentity

section LevelTwo

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_isLocalFlow_augVF_of_C2
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (p₀ : E × (E →L[ℝ] E)) :
    ∃ (R : ℝ≥0) (ε : ℝ) (_ : 0 < R) (_ : 0 < ε)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      IsLocalFlow (augmentedVectorField f) t₀ p₀ R (t₀ - ε) (t₀ + ε) aΦ := by
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  exact exists_isLocalFlow_of_contDiffOn_univ (augmentedVectorField f) h_augVF_C1 t₀ p₀

theorem contDiffOn_flow_of_isLocalFlow_C2_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y 1) :
    ContDiffOn ℝ 2 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hΦ_C1 : ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    norm_num
    exact hf_C2
  have h_step := contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid
    hT_mid_lt_out hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
    (k := (1 : ℕ∞)) hf_succ hΦ_C1 hY
  norm_num at h_step
  exact h_step

end LevelTwo

section AugFlowProjection

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

def fromAugFlow (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)) :
    E × ℝ → (E →L[ℝ] E) :=
  fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).2

omit [CompleteSpace E] in
@[simp]
lemma fromAugFlow_apply (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (x : E) (t : ℝ) :
    fromAugFlow aΦ (x, t) = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := rfl

omit [CompleteSpace E] in
theorem contDiffOn_fromAugFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {k : ℕ∞} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} {U : Set (E × ℝ)}
    (haΦ : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U Ω) :
    ContDiffOn ℝ k (fromAugFlow aΦ) U := by
  have h_embed_smooth : ContDiff ℝ (k : ℕ∞)
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) := by
    refine ContDiff.prodMk ?_ contDiff_snd
    refine ContDiff.prodMk contDiff_fst ?_
    exact contDiff_const
  have h_embed_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) U :=
    h_embed_smooth.contDiffOn
  have hcomp : ContDiffOn ℝ k (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U :=
    haΦ.comp h_embed_Ck hmap
  have hsnd_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : E × (E →L[ℝ] E) => p.2) := contDiff_snd
  have hsnd_Ck : ContDiffOn ℝ k (fun p : E × (E →L[ℝ] E) => p.2)
      (Set.univ : Set (E × (E →L[ℝ] E))) := hsnd_smooth.contDiffOn
  have hmaps : MapsTo (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U
      (Set.univ : Set (E × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hfinal : ContDiffOn ℝ k
      ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2)))) U :=
    hsnd_Ck.comp hcomp hmaps
  have heq : ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2))))
      = fromAugFlow aΦ := by
    funext q
    rfl
  rw [heq] at hfinal
  exact hfinal

end AugFlowProjection

section UnconditionalAbstract

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_succ_of_augFlow_candidate
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hY_Ck : ContDiffOn ℝ k (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugFlow haΦ_Ck hmap
  have hY : IsVariationalFlowProjection hΦ T ρ (fromAugFlow aΦ) k :=
    { contDiffOn := hY_Ck, fderiv_eq := h_fderiv_eq }
  exact contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hY

end UnconditionalAbstract

section AggregatedPublic

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_flow_of_augFlow_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (aΦ_seq : ℕ → (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (Ω_seq : ℕ → Set ((E × (E →L[ℝ] E)) × ℝ))
    (haΦ_Ck : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (aΦ_seq j) (Ω_seq j))
    (hmap_seq : ∀ j : ℕ, j + 1 ≤ k →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) (Ω_seq j))
    (h_fderiv_eq_seq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow (aΦ_seq j) q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun j => fromAugFlow (aΦ_seq j) with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  refine
  { contDiffOn := contDiffOn_fromAugFlow (haΦ_Ck j hj) (hmap_seq j hj),
    fderiv_eq := h_fderiv_eq_seq j hj }

end AggregatedPublic

section OperatorVariational

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
lemma hasDerivWithinAt_apply {Z Z' : ℝ → (E →L[ℝ] E)} {s : Set ℝ} {t : ℝ} {δ : E}
    (hZ : HasDerivWithinAt Z (Z' t) s t) :
    HasDerivWithinAt (fun τ => Z τ δ) ((Z' t) δ) s t := by
  set applyδ : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E δ
  have happ : HasFDerivAt applyδ applyδ (Z t) := applyδ.hasFDerivAt
  have hZ_fd : HasFDerivWithinAt Z
      (ContinuousLinearMap.toSpanSingleton ℝ (Z' t)) s t := hZ.hasFDerivWithinAt
  have happ_fd := happ.comp_hasFDerivWithinAt t hZ_fd
  have heq : applyδ.comp (ContinuousLinearMap.toSpanSingleton ℝ (Z' t))
      = ContinuousLinearMap.toSpanSingleton ℝ ((Z' t) δ) := by
    apply ContinuousLinearMap.ext
    intro r
    simp [applyδ, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
  rw [heq] at happ_fd
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact happ_fd

omit [CompleteSpace E] in
theorem isVariationalSolutionOn_apply
    {T : ℝ}
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    (δ : E) :
    IsVariationalSolutionOn f α δ t₀ (fun s => Z s δ) (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨?_, ?_⟩
  · have : Z t₀ δ = ContinuousLinearMap.id ℝ E δ := by rw [hZ_init]
    simpa using this
  · intro t ht
    have hZ_d := hZ_deriv t ht
    have happ := hasDerivWithinAt_apply (Z := Z)
      (Z' := fun s => (fderiv ℝ (f s) (α s)).comp (Z s)) (δ := δ) hZ_d
    have hsimp : ((fderiv ℝ (f t) (α t)).comp (Z t)) δ
        = (fderiv ℝ (f t) (α t)) (Z t δ) := by rfl
    rw [hsimp] at happ
    exact happ

theorem Z_eq_variationalLinearMapAt
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    Z t = variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht := by
  apply ContinuousLinearMap.ext
  intro δ
  have h_Z_sol := isVariationalSolutionOn_apply (T := T) (Z := Z) hZ_init hZ_deriv δ
  have h_var_sol := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont h_Z_sol h_var_sol
  have hZδ_t : Z t δ
      = variationalSolutionFun (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd δ t :=
    h_eq ht
  rw [hZδ_t]
  exact (variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht δ).symm

end OperatorVariational

section AugFlowVariationalIdentification

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem augFlow_snd_eq_variationalLinearMapAt
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    {p₀ : E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ p₀ R tmin' tmax' aΦ)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    {x : E} (hx : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f t) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT hM hMT hA_cont hA_bd ht := by
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set orbit : ℝ → E × (E →L[ℝ] E) := fun s => aΦ ⟨p, s⟩ with horbit_def
  set Z : ℝ → E →L[ℝ] E := fun s => (orbit s).2 with hZ_def
  set α : ℝ → E := fun s => (orbit s).1 with hα_def
  have hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E := by
    have h_init : orbit t₀ = p := haΦ.apply_initial p hx
    change (orbit t₀).2 = ContinuousLinearMap.id ℝ E
    rw [h_init]
  have h_orbit_deriv : ∀ s ∈ Icc tmin' tmax',
      HasDerivWithinAt orbit (augmentedVectorField f s (orbit s)) (Icc tmin' tmax') s :=
    fun s hs => haΦ.hasDerivWithinAt p hx s hs
  have h_orbit_deriv' : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt orbit (augmentedVectorField f s (orbit s)) (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    exact (h_orbit_deriv s (hsub hs)).mono hsub
  have hZ_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f s) (α s)).comp (Z s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have h := h_orbit_deriv' s hs
    set sndCLM : (E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
      ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)
    have h_fd := h.hasFDerivWithinAt
    have h_snd_at := (sndCLM.hasFDerivAt).comp_hasFDerivWithinAt s h_fd
    have heq : sndCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ
      (augmentedVectorField f s (orbit s)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augmentedVectorField f s (orbit s)).2) := by
      apply ContinuousLinearMap.ext
      intro r
      change (sndCLM (r • augmentedVectorField f s (orbit s)))
        = r • (augmentedVectorField f s (orbit s)).2
      change (r • augmentedVectorField f s (orbit s)).2 = r • (augmentedVectorField f s (orbit s)).2
      rfl
    rw [heq] at h_snd_at
    have h_aug_snd : (augmentedVectorField f s (orbit s)).2
        = (fderiv ℝ (f s) (α s)).comp (Z s) := rfl
    rw [h_aug_snd] at h_snd_at
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact h_snd_at
  exact Z_eq_variationalLinearMapAt hT hM hMT hA_cont hA_bd hZ_init hZ_deriv ht

end AugFlowVariationalIdentification

end Poincare.ODE.LocalFlow

end
