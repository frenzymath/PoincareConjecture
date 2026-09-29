/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/VariationalMapContDiffOnK.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development. The development is split across local modules.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.HigherRegularity.VariationalMapContDiffOnK.Foundations

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace Poincare.ODE.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section UniformContainment

variable [FiniteDimensional ℝ E]
variable {x₀ : E} {t₀ tmin tmax : ℝ}

omit [CompleteSpace E] in
theorem exists_uniform_time_containment
    {ρ₀ : ℝ} (Ψ : E × ℝ → E)
    (hΨ_cont : ContinuousOn Ψ (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax))
    (hΨ_init : ∀ x ∈ closedBall x₀ ρ₀, Ψ (x, t₀) = x)
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hρ₀_pos : 0 < ρ₀)
    {ρ_b : ℝ} (hρ_b_pos : 0 < ρ_b) :
    ∃ ρ_c > 0, ∃ T_c > 0, ρ_c ≤ ρ₀ ∧ Icc (t₀ - T_c) (t₀ + T_c) ⊆ Icc tmin tmax ∧
      ∀ x ∈ closedBall x₀ ρ_c, ∀ t ∈ Ioo (t₀ - T_c) (t₀ + T_c),
        Ψ (x, t) ∈ closedBall x₀ ρ_b := by
  have hcompact : IsCompact (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax) :=
    (isCompact_closedBall x₀ ρ₀).prod isCompact_Icc
  have huc : UniformContinuousOn Ψ (closedBall x₀ ρ₀ ×ˢ Icc tmin tmax) :=
    hcompact.uniformContinuousOn_of_continuous hΨ_cont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (ρ_b / 2) (by positivity)
  set ρ_c : ℝ := min ρ₀ (ρ_b / 2) with hρ_c_def
  have hρ_c_pos : 0 < ρ_c := lt_min hρ₀_pos (by positivity)
  have hρ_c_le : ρ_c ≤ ρ₀ := min_le_left _ _
  have hρ_c_le_b : ρ_c ≤ ρ_b / 2 := min_le_right _ _
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_c : ℝ := min (δ / 2) (d / 2) with hT_c_def
  have hT_c_pos : 0 < T_c := lt_min (by linarith) (by linarith)
  have hT_c_lt_δ : T_c < δ := by
    calc T_c ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hsub : Icc (t₀ - T_c) (t₀ + T_c) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have hh : d ≤ t₀ - tmin := min_le_left _ _
      have ht : T_c ≤ d / 2 := min_le_right _ _
      linarith
    · have hh : d ≤ tmax - t₀ := min_le_right _ _
      have ht : T_c ≤ d / 2 := min_le_right _ _
      linarith
  refine ⟨ρ_c, hρ_c_pos, T_c, hT_c_pos, hρ_c_le, hsub, ?_⟩
  intro x hx t ht
  have hx₀ : x ∈ closedBall x₀ ρ₀ := closedBall_subset_closedBall hρ_c_le hx
  have ht_Icc : t ∈ Icc tmin tmax := hsub (Ioo_subset_Icc_self ht)
  have ht₀_Icc : t₀ ∈ Icc tmin tmax := ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩
  have hmem1 : ((x, t) : E × ℝ) ∈ closedBall x₀ ρ₀ ×ˢ Icc tmin tmax := ⟨hx₀, ht_Icc⟩
  have hmem2 : ((x, t₀) : E × ℝ) ∈ closedBall x₀ ρ₀ ×ˢ Icc tmin tmax := ⟨hx₀, ht₀_Icc⟩
  have hdist_xt : dist ((x, t) : E × ℝ) (x, t₀) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, max_eq_right (dist_nonneg)]
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1, hT_c_lt_δ], by linarith [ht.2, hT_c_lt_δ]⟩
  have hclose : dist (Ψ (x, t)) (Ψ (x, t₀)) < ρ_b / 2 := hδ _ hmem1 _ hmem2 hdist_xt
  rw [hΨ_init x hx₀] at hclose
  rw [mem_closedBall]
  have hx_dist : dist x x₀ ≤ ρ_b / 2 := le_trans (mem_closedBall.mp hx) hρ_c_le_b
  calc dist (Ψ (x, t)) x₀ ≤ dist (Ψ (x, t)) x + dist x x₀ := dist_triangle _ _ _
    _ ≤ ρ_b / 2 + ρ_b / 2 := add_le_add (le_of_lt hclose) hx_dist
    _ = ρ_b := by ring

end UniformContainment

section OrbitUniqueness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem orbit_unique_Ioo
    {a b : ℝ} {y₁ y₂ : ℝ → E} {K : ℝ≥0} {c : E} {ρ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (closedBall c ρ))
    (hy₁ : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t)
    (hy₂ : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t)
    (hy₁_mem : ∀ t ∈ Ioo a b, y₁ t ∈ closedBall c ρ)
    (hy₂_mem : ∀ t ∈ Ioo a b, y₂ t ∈ closedBall c ρ)
    (hinit : y₁ t₀ = y₂ t₀) :
    EqOn y₁ y₂ (Ioo a b) := by
  exact ODE_solution_unique_of_mem_Ioo (v := fun t y => f t y)
    (s := fun _ => closedBall c ρ) (K := K)
    hLip ht₀
    (fun t ht => ⟨hy₁ t ht, hy₁_mem t ht⟩)
    (fun t ht => ⟨hy₂ t ht, hy₂_mem t ht⟩)
    hinit

omit [CompleteSpace E] in
theorem augFlow_fst_eq_flow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {p₀ : E × (E →L[ℝ] E)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ p₀ R tmin' tmax' aΦ)
    {a b : ℝ} {K : ℝ≥0} {c : E} {ρ_b : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (ha_sub : Ioo a b ⊆ Icc tmin tmax) (ha_sub' : Ioo a b ⊆ Icc tmin' tmax')
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (closedBall c ρ_b))
    {x : E} (hx : x ∈ closedBall x₀ (r : ℝ))
    (hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hy₁_mem : ∀ t ∈ Ioo a b, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 ∈ closedBall c ρ_b)
    (hy₂_mem : ∀ t ∈ Ioo a b, Φ ⟨x, t⟩ ∈ closedBall c ρ_b) :
    ∀ t ∈ Ioo a b, (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 = Φ ⟨x, t⟩ := by
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set y₁ : ℝ → E := fun s => (aΦ ⟨p, s⟩).1 with hy₁_def
  set y₂ : ℝ → E := fun s => Φ ⟨x, s⟩ with hy₂_def
  have hy₁_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₁ (f t (y₁ t)) t := by
    intro t ht
    have h_orbit := haΦ.hasDerivWithinAt p hxp t (ha_sub' ht)
    set fstCLM : (E × (E →L[ℝ] E)) →L[ℝ] E := ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)
    have h_fd := h_orbit.hasFDerivWithinAt
    have h_fst_at := (fstCLM.hasFDerivAt).comp_hasFDerivWithinAt t h_fd
    have heq : fstCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (augmentedVectorField f t (aΦ ⟨p, t⟩)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augmentedVectorField f t (aΦ ⟨p, t⟩)).1) := by
      apply ContinuousLinearMap.ext
      intro s
      change fstCLM (s • augmentedVectorField f t (aΦ ⟨p, t⟩)) = s •
        (augmentedVectorField f t (aΦ ⟨p, t⟩)).1
      change (s • augmentedVectorField f t (aΦ ⟨p, t⟩)).1 = s •
        (augmentedVectorField f t (aΦ ⟨p, t⟩)).1
      rfl
    rw [heq] at h_fst_at
    have h_aug_fst : (augmentedVectorField f t (aΦ ⟨p, t⟩)).1 = f t (y₁ t) := rfl
    rw [h_aug_fst] at h_fst_at
    have h_within : HasDerivWithinAt y₁ (f t (y₁ t)) (Icc tmin' tmax') t := by
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      exact h_fst_at
    exact (h_within.mono ha_sub').hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hy₂_deriv : ∀ t ∈ Ioo a b, HasDerivAt y₂ (f t (y₂ t)) t := by
    intro t ht
    have h_within := hΦ.hasDerivWithinAt x hx t (ha_sub ht)
    exact (h_within.mono ha_sub).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hinit : y₁ t₀ = y₂ t₀ := by
    have h1 : y₁ t₀ = x := by
      change (aΦ ⟨p, t₀⟩).1 = x
      rw [haΦ.apply_initial p hxp]
    have h2 : y₂ t₀ = x := by
      change Φ ⟨x, t₀⟩ = x
      exact hΦ.apply_initial x hx
    rw [h1, h2]
  exact orbit_unique_Ioo ht₀ hLip hy₁_deriv hy₂_deriv hy₁_mem hy₂_mem hinit

end OrbitUniqueness

section VariationalLinearMapCongr

variable {f : ℝ → E → E} {α₁ α₂ : ℝ → E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem IsVariationalSolutionOn.congr_central
    {T : ℝ} {δ : E} {y : ℝ → E}
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hy : IsVariationalSolutionOn f α₁ δ t₀ y (Icc (t₀ - T) (t₀ + T))) :
    IsVariationalSolutionOn f α₂ δ t₀ y (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨hy.1, ?_⟩
  intro t ht
  have hd := hy.2 t ht
  rwa [hαeq ht] at hd

theorem variationalLinearMapAt_congr_central
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hαeq : EqOn α₁ α₂ (Icc (t₀ - T) (t₀ + T)))
    (hA_cont₁ : ContinuousOn (fun t => fderiv ℝ (f t) (α₁ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₁ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₁ t)‖ ≤ M)
    (hA_cont₂ : ContinuousOn (fun t => fderiv ℝ (f t) (α₂ t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd₂ : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α₂ t)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    variationalLinearMapAt (f := f) (α := α₁) (t₀ := t₀) hT hM hMT hA_cont₁ hA_bd₁ ht
      = variationalLinearMapAt (f := f) (α := α₂) (t₀ := t₀) hT hM hMT hA_cont₂ hA_bd₂ ht := by
  apply ContinuousLinearMap.ext
  intro δ
  have h₁ := variationalSolutionFun_isSolution hT hM hMT hA_cont₁ hA_bd₁ δ
  have h₂ := variationalSolutionFun_isSolution hT hM hMT hA_cont₂ hA_bd₂ δ
  have h₁' : IsVariationalSolutionOn f α₂ δ t₀
      (variationalSolutionFun hT hM hMT hA_cont₁ hA_bd₁ δ) (Icc (t₀ - T) (t₀ + T)) :=
    IsVariationalSolutionOn.congr_central hαeq h₁
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont₂ h₁' h₂
  rw [variationalLinearMapAt_apply, variationalLinearMapAt_apply]
  exact h_eq ht

end VariationalLinearMapCongr

section SpatialPieceVariational

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem spatialPieceFn_eq_variationalLinearMapAt
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    spatialPieceFn Φ (x, t)
      = variationalLinearMapAt (f := f) (α := fun s => Φ ⟨x, s⟩) (t₀ := t₀) hT hM hMT
          (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
              rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
            (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub)
          (fun τ hτ => hA_bd x hx τ hτ) (Ioo_subset_Icc_self ht) := by
  have hfd_at := hasFDerivAt_flow_jointly_at hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  have hfd_eq := hfd_at.fderiv
  rw [spatialPieceFn_apply, hfd_eq]
  exact ContinuousLinearMap.coprod_comp_inl _ _

end SpatialPieceVariational

section SpatialPieceAugFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem spatialPieceFn_eq_fromAugFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {x : E} (hx : x ∈ closedBall x₀ (ρ : ℝ))
    (hy₁_mem : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hy₂_mem : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'), Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    {t : ℝ} (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
    spatialPieceFn Φ (x, t) = fromAugFlow aΦ (x, t) := by
  have hx_le : dist x x₀ ≤ (ρ : ℝ) := by rw [mem_closedBall] at hx; exact hx
  have hx_r : x ∈ closedBall x₀ (r : ℝ) :=
    mem_closedBall.mpr (by linarith [r'.coe_nonneg])
  have hxp : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall (x₀, ContinuousLinearMap.id ℝ E)
    (R : ℝ) := by
    rw [mem_closedBall, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist x x₀ ≤ (ρ : ℝ) := hx_le
      _ ≤ (R : ℝ) := hρR
  set α₁ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα₁_def
  set α₂ : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 with hα₂_def
  have ht₀_O : t₀ ∈ Ioo (t₀ - T') (t₀ + T') := ⟨by linarith, by linarith⟩
  have h_orbit_eq : ∀ s ∈ Ioo (t₀ - T') (t₀ + T'), α₂ s = α₁ s :=
    augFlow_fst_eq_flow hΦ haΦ ht₀_O hsubO hsubO' hLip hx_r hxp hy₁_mem hy₂_mem
  have hαeq : EqOn α₂ α₁ (Icc (t₀ - T) (t₀ + T)) := by
    intro s hs
    have hs_O : s ∈ Ioo (t₀ - T') (t₀ + T') :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact h_orbit_eq s hs_O
  have h_sp := spatialPieceFn_eq_variationalLinearMapAt hΦ hf_C1 hT hM hMT hsub hr' hρρ' hA_bd hx ht
  set hA_cont₁ : ContinuousOn (fun s => fderiv ℝ (f s) (α₁ s)) (Icc (t₀ - T) (t₀ + T)) :=
    (((hΦ.restrict_center_of_norm_le (x₁ := x) (r' := r') (by
        rw [mem_closedBall] at hx; linarith)).continuousOn_fderiv_along_orbit hf_C1 x
      (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hr')))).mono hsub) with hA_cont₁_def
  set hA_bd₁ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₁ s)‖ ≤ M :=
    (fun τ hτ => hA_bd x hx τ hτ) with hA_bd₁_def
  have hA_cont₂ : ContinuousOn (fun s => fderiv ℝ (f s) (α₂ s)) (Icc (t₀ - T) (t₀ + T)) := by
    apply hA_cont₁.congr
    intro s hs
    change fderiv ℝ (f s) (α₂ s) = fderiv ℝ (f s) (α₁ s)
    rw [hαeq hs]
  have hA_bd₂ : ∀ s ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f s) (α₂ s)‖ ≤ M := by
    intro s hs
    rw [hαeq hs]
    exact hA_bd₁ s hs
  have h_aug := augFlow_snd_eq_variationalLinearMapAt haΦ hT hM hMT hsub'
    hxp hA_cont₂ hA_bd₂ (Ioo_subset_Icc_self ht)
  have h_congr := variationalLinearMapAt_congr_central hT hM hMT hαeq
    hA_cont₂ hA_bd₂ hA_cont₁ hA_bd₁ (Ioo_subset_Icc_self ht)
  rw [fromAugFlow_apply]
  rw [h_sp]
  rw [h_aug, h_congr]

end SpatialPieceAugFlow

section VariationalLinearMapSmooth

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem contDiffOn_variationalLinearMap
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    {T T' M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1) (hTT' : T < T')
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax)
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ r' : ℝ≥0} (hr' : 0 < r')
    (hρρ' : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) :
    ContDiffOn ℝ k (spatialPieceFn Φ) ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have h_fromAug_Ck : ContDiffOn ℝ k (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugFlow haΦ_Ck hmap
  have h_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      spatialPieceFn Φ q = fromAugFlow aΦ q := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    rw [mem_ball] at hq_x
    obtain ⟨x, t⟩ := q
    have hx_cb : x ∈ closedBall x₀ (ρ : ℝ) := mem_closedBall.mpr (le_of_lt hq_x)
    exact spatialPieceFn_eq_fromAugFlow hΦ haΦ hf_C1 hT hM hMT hTT' hsub hsub' hsubO hsubO'
      hLip hr' hρρ' hρR hA_bd hx_cb (hcontain₁ x hx_cb) (hcontain₂ x hx_cb) hq_t
  exact h_fromAug_Ck.congr h_eq

theorem contDiffOn_flow_succ_via_augFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T T' M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1) (hT_lt' : T < T') (hTT'_out : T' ≤ T_out)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    (hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    (hsubO' : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin' tmax')
    {K : ℝ≥0} {ρ_b : ℝ}
    (hLip : ∀ t ∈ Ioo (t₀ - T') (t₀ + T'), LipschitzOnWith K (f t) (closedBall x₀ ρ_b))
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ)) (hρR : (ρ : ℝ) ≤ (R : ℝ))
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ ρ_b)
    (hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T') (t₀ + T'),
      Φ ⟨x, s⟩ ∈ closedBall x₀ ρ_b)
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      exact_mod_cast this
    have h := hf_succ.of_le h_le
    simpa using h
  have hT_pos : 0 < T := hT
  have hsub_T : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_T_tmax : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax := hsub_T.trans hsub
  have hsubO_tmax : Ioo (t₀ - T') (t₀ + T') ⊆ Icc tmin tmax := by
    intro s hs
    exact hsub (Icc_subset_Icc (by linarith [hs.1]) (by linarith [hs.2]) (Ioo_subset_Icc_self hs))
  have hMT : M * T < 1 := lt_of_le_of_lt (by nlinarith [hM, le_of_lt hT_lt_mid]) hMT_mid
  have hA_bd_inner : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ τ ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := by
    intro x hx τ hτ
    refine hA_bd x ?_ τ (hsub_T hτ)
    exact closedBall_subset_closedBall
      (le_trans (le_of_lt hρ_lt_mid) (le_of_lt hρ_mid_lt_out)) hx
  have hρρ'_inner : (ρ : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by
    have := hρ_lt_mid; linarith
  have hLsp_Ck : ContDiffOn ℝ k (spatialPieceFn Φ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_variationalLinearMap hΦ haΦ hf_C1 haΦ_Ck hT hM hMT hT_lt' hsub_T_tmax hsub'
      hsubO_tmax hsubO' hLip hr' hρρ'_inner hρR hmap hcontain₁ hcontain₂ hA_bd_inner
  have hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) :=
    fderiv_flow_eq_coprod_spatialPiece hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hA_bd
  exact contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hLsp_Ck hLsp_eq

end VariationalLinearMapSmooth

section UnconditionalC1

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_contDiffOn_flow_C1 [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ 1 Φ U := by
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ := exists_flow_nesting_data hΦ hf ht₀ hr_pos
  exact exists_contDiffOn_flow_of_contDiff hΦ (le_refl 1) hf hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd

end UnconditionalC1

section NeighbourhoodReconciliation

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem exists_basic_nhds_subset_aux {U : Set (E × ℝ)}
    (hU_open : IsOpen U) (hU_mem : (x₀, t₀) ∈ U) :
    ∃ ρ₁ > 0, ∃ T₁ > 0, ball x₀ ρ₁ ×ˢ Ioo (t₀ - T₁) (t₀ + T₁) ⊆ U := by
  have hU_nhds : U ∈ 𝓝 ((x₀, t₀) : E × ℝ) := hU_open.mem_nhds hU_mem
  rw [nhds_prod_eq] at hU_nhds
  obtain ⟨S, hS, V, hV, hSV⟩ := Filter.mem_prod_iff.mp hU_nhds
  obtain ⟨ρ₁, hρ₁_pos, hρ₁_sub⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨T₁, hT₁_pos, hT₁_sub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ₁, hρ₁_pos, T₁, hT₁_pos, ?_⟩
  intro p hp; apply hSV; rcases hp with ⟨hp1, hp2⟩
  refine ⟨hρ₁_sub hp1, hT₁_sub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩

omit [CompleteSpace E] in
theorem exists_embed_caps_aux
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} (hΩ_open : IsOpen Ω)
    (hΩ_mem : ((x₀, ContinuousLinearMap.id ℝ E), t₀) ∈ Ω) :
    ∃ ρ_a > 0, ∃ T_a > 0, ∀ (ρ T : ℝ), ρ ≤ ρ_a → T ≤ T_a →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        (ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω := by
  have hΩ_nhds : Ω ∈ 𝓝 (((x₀, ContinuousLinearMap.id ℝ E), t₀)) := hΩ_open.mem_nhds hΩ_mem
  rw [nhds_prod_eq] at hΩ_nhds
  obtain ⟨S, hS, V, hV, hSV⟩ := Filter.mem_prod_iff.mp hΩ_nhds
  obtain ⟨ρ_a, hρ_a_pos, hρ_a_sub⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨T_a, hT_a_pos, hT_a_sub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ρ_a, hρ_a_pos, T_a, hT_a_pos, ?_⟩
  intro ρ T hρ hT p hp; apply hSV; rcases hp with ⟨hp1, hp2⟩
  rw [Metric.mem_ball] at hp1
  refine ⟨hρ_a_sub ?_, hT_a_sub ?_⟩
  · rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist p.1 x₀ < ρ := hp1
      _ ≤ ρ_a := hρ
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hp2.1, hT], by linarith [hp2.2, hT]⟩

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem exists_flow_nesting_data_capped
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ))
    {ρcap Tcap : ℝ} (hρcap : 0 < ρcap) (hTcap : 0 < Tcap) :
    ∃ (T_out T_mid T M : ℝ) (ρ_out ρ_mid ρ r' : ℝ≥0),
      0 < T ∧ T < T_mid ∧ T_mid < T_out ∧ 0 ≤ M ∧ M * T_mid < 1 ∧ 0 < (r' : ℝ) ∧
      0 < (ρ : ℝ) ∧ (ρ : ℝ) < (ρ_mid : ℝ) ∧ (ρ_mid : ℝ) < (ρ_out : ℝ) ∧
      (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) ∧ (ρ_out : ℝ) ≤ (r : ℝ) ∧
      (ρ_out : ℝ) ≤ ρcap ∧ T_out ≤ Tcap ∧
      Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax ∧
      (∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
        ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M) := by
  set rb : ℝ := min (r : ℝ) ρcap with hrb_def
  have hrb_pos : 0 < rb := lt_min hr_pos hρcap
  have hrb_le_r : rb ≤ (r : ℝ) := min_le_left _ _
  have hrb_le_cap : rb ≤ ρcap := min_le_right _ _
  set ρ_out : ℝ≥0 := ⟨rb / 2, by positivity⟩ with hρout_def
  set ρ_mid : ℝ≥0 := ⟨rb / 4, by positivity⟩ with hρmid_def
  set ρ : ℝ≥0 := ⟨rb / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨rb / 2, by positivity⟩ with hr'_def
  have hρ_out_coe : (ρ_out : ℝ) = rb / 2 := rfl
  have hρ_mid_coe : (ρ_mid : ℝ) = rb / 4 := rfl
  have hρ_coe : (ρ : ℝ) = rb / 8 := rfl
  have hr'_coe : (r' : ℝ) = rb / 2 := rfl
  have hρ_pos : 0 < (ρ : ℝ) := by rw [hρ_coe]; linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by rw [hρ_coe, hρ_mid_coe]; linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by rw [hρ_mid_coe, hρ_out_coe]; linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ) := by
    rw [hρ_mid_coe, hr'_coe]; nlinarith [hrb_le_r, hrb_pos]
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ) := by rw [hρ_out_coe]; nlinarith [hrb_le_r, hrb_pos]
  have hρ_out_le_cap : (ρ_out : ℝ) ≤ ρcap := by rw [hρ_out_coe]; nlinarith [hrb_le_cap, hrb_pos]
  have hr'_pos : 0 < (r' : ℝ) := by rw [hr'_coe]; linarith
  set d : ℝ := min (t₀ - tmin) (tmax - t₀) with hd_def
  have hd_pos : 0 < d := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  set T_out : ℝ := min (d / 2) (Tcap / 2) with hT_out_def
  have hT_out_pos : 0 < T_out := lt_min (by linarith) (by linarith)
  have hT_out_le_cap : T_out ≤ Tcap := by
    calc T_out ≤ Tcap / 2 := min_le_right _ _
      _ ≤ Tcap := by linarith
  have hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax := by
    apply Icc_subset_Icc
    · have hh : d ≤ t₀ - tmin := min_le_left _ _
      have ht : T_out ≤ d / 2 := min_le_left _ _
      linarith
    · have hh : d ≤ tmax - t₀ := min_le_right _ _
      have ht : T_out ≤ d / 2 := min_le_left _ _
      linarith
  obtain ⟨M, hM_nonneg, hM_bd⟩ :=
    exists_norm_fderiv_le_along_flow_joint hΦ hf (ρ := (ρ_out : ℝ))
      (NNReal.coe_nonneg ρ_out) hρ_out_le_r
  have hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M := fun x hx τ hτ => hM_bd x hx τ (hsub hτ)
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
    calc M * T_mid ≤ M * (1 / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hle hM_nonneg
      _ = M / (2 * (M + 1)) := by ring
      _ < 1 := by rw [div_lt_one hM1_pos]; linarith
  exact ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT_pos, hT_lt_mid, hT_mid_lt_out,
    hM_nonneg, hMT_mid, hr'_pos, hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r,
    hρ_out_le_cap, hT_out_le_cap, hsub, hA_bd⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem continuousOn_augFlow_fst
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    {ρ₀ : ℝ} (hρ₀_le : ρ₀ ≤ (R : ℝ)) :
    ContinuousOn (fun q : E × ℝ => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).1)
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax') := by
  have hembed : ContinuousOn (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax') :=
    ((continuousOn_fst).prodMk continuousOn_const).prodMk continuousOn_snd
  have hmaps : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      (closedBall x₀ ρ₀ ×ˢ Icc tmin' tmax')
      (closedBall (x₀, ContinuousLinearMap.id ℝ E) (R : ℝ) ×ˢ Icc tmin' tmax') := by
    intro p hp; rcases hp with ⟨hp1, hp2⟩
    refine ⟨?_, hp2⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    simp only [dist_self, max_eq_left (dist_nonneg)]
    calc dist p.1 x₀ ≤ ρ₀ := mem_closedBall.mp hp1
      _ ≤ (R : ℝ) := hρ₀_le
  exact continuous_fst.comp_continuousOn (haΦ.continuousOn.comp hembed hmaps)

end NeighbourhoodReconciliation

section CkDriver

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
variable [FiniteDimensional ℝ E]

theorem exists_contDiffOn_flow_succ_driver
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R tmin' tmax'
      aΦ)
    (ht₀' : t₀ ∈ Ioo tmin' tmax') (hR_pos : 0 < (R : ℝ))
    {k : ℕ∞} (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hΩ_open : IsOpen Ω) (hΩ_mem : ((x₀, ContinuousLinearMap.id ℝ E), t₀) ∈ Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr_pos : 0 < (r : ℝ))
    (hΦ_prev : ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ k Φ U) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (k + 1) Φ U := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact bot_le
      exact_mod_cast this
    simpa using hf_succ.of_le h_le
  obtain ⟨U, hU_open, hU_mem, hU_Ck⟩ := hΦ_prev
  obtain ⟨ρ_p, hρ_p_pos, T_p, hT_p_pos, hbox_p⟩ := exists_basic_nhds_subset_aux hU_open hU_mem
  obtain ⟨ρ_a, hρ_a_pos, T_a, hT_a_pos, hembed⟩ := exists_embed_caps_aux hΩ_open hΩ_mem
  have hΦ_cont_box : ContinuousOn Φ (closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) := hΦ.continuousOn
  have hΦ_init : ∀ x ∈ closedBall x₀ (r : ℝ), Φ (x, t₀) = x := hΦ.apply_initial
  obtain ⟨ρ_c2, hρ_c2_pos, T_c2, hT_c2_pos, hρ_c2_le, hsub_c2, hcontain_Φ⟩ :=
    exists_uniform_time_containment (x₀ := x₀) (ρ₀ := (r : ℝ)) (ρ_b := (r : ℝ)) Φ
      hΦ_cont_box hΦ_init ht₀ hr_pos hr_pos
  set Ψaug : E × ℝ → E := fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).1 with hΨaug_def
  have hΨaug_cont : ContinuousOn Ψaug (closedBall x₀ (R : ℝ) ×ˢ Icc tmin' tmax') :=
    continuousOn_augFlow_fst haΦ (le_refl _)
  have hΨaug_init : ∀ x ∈ closedBall x₀ (R : ℝ), Ψaug (x, t₀) = x := by
    intro x hx
    have hxp : (x, ContinuousLinearMap.id ℝ E) ∈
        closedBall (x₀, ContinuousLinearMap.id ℝ E) (R : ℝ) := by
      rw [mem_closedBall, Prod.dist_eq]
      simp only [dist_self, max_eq_left (dist_nonneg)]
      exact mem_closedBall.mp hx
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hxp]
  obtain ⟨ρ_c1, hρ_c1_pos, T_c1, hT_c1_pos, hρ_c1_le, hsub_c1, hcontain_aug⟩ :=
    exists_uniform_time_containment (x₀ := x₀) (ρ₀ := (R : ℝ)) (ρ_b := (r : ℝ)) Ψaug
      hΨaug_cont hΨaug_init ht₀' hR_pos hr_pos
  set ρcap : ℝ := min (min ρ_a ρ_p) (min ρ_c1 ρ_c2) with hρcap_def
  have hρcap_pos : 0 < ρcap := lt_min (lt_min hρ_a_pos hρ_p_pos) (lt_min hρ_c1_pos hρ_c2_pos)
  set Tcap : ℝ := min (min T_a T_p) (min T_c1 T_c2) with hTcap_def
  have hTcap_pos : 0 < Tcap := lt_min (lt_min hT_a_pos hT_p_pos) (lt_min hT_c1_pos hT_c2_pos)
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r', hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid,
    hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out, hρρ', hρ_out_le_r, hρ_out_le_cap, hT_out_le_cap,
    hsub_out, hA_bd⟩ := exists_flow_nesting_data_capped hΦ hf_C1 ht₀ hr_pos hρcap_pos hTcap_pos
  have hρcap_le_ρa : ρcap ≤ ρ_a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρcap_le_ρp : ρcap ≤ ρ_p := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρcap_le_ρc1 : ρcap ≤ ρ_c1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρcap_le_ρc2 : ρcap ≤ ρ_c2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hTcap_le_Ta : Tcap ≤ T_a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hTcap_le_Tp : Tcap ≤ T_p := le_trans (min_le_left _ _) (min_le_right _ _)
  have hTcap_le_Tc1 : Tcap ≤ T_c1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hTcap_le_Tc2 : Tcap ≤ T_c2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρ_lt_out : (ρ : ℝ) < (ρ_out : ℝ) := lt_trans hρ_lt_mid hρ_mid_lt_out
  have hρ_le_cap : (ρ : ℝ) ≤ ρcap := le_trans (le_of_lt hρ_lt_out) hρ_out_le_cap
  have hT_lt_out : T < T_out := lt_trans hT_lt_mid hT_mid_lt_out
  have hT_le_cap : T ≤ Tcap := le_trans (le_of_lt hT_lt_out) hT_out_le_cap
  have hTmid_le_cap : T_mid ≤ Tcap := le_trans (le_of_lt hT_mid_lt_out) hT_out_le_cap
  have hρR : (ρ : ℝ) ≤ (R : ℝ) := le_trans (le_trans hρ_le_cap hρcap_le_ρc1) hρ_c1_le
  have hT_le_Tc1 : T ≤ T_c1 := le_trans hT_le_cap hTcap_le_Tc1
  have hsub' : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax' :=
    (Icc_subset_Icc (by linarith) (by linarith)).trans hsub_c1
  have hTmid_le_Tc1 : T_mid ≤ T_c1 := le_trans hTmid_le_cap hTcap_le_Tc1
  have hsubO' : Ioo (t₀ - T_mid) (t₀ + T_mid) ⊆ Icc tmin' tmax' := by
    intro s hs
    exact hsub_c1 (Icc_subset_Icc (by linarith) (by linarith) (Ioo_subset_Icc_self hs))
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closedBall_of_C1 hf_C1 x₀ (r : ℝ)
    (t₀ - T_out) (t₀ + T_out) (by linarith)
  have hLip : ∀ t ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      LipschitzOnWith K (f t) (closedBall x₀ (r : ℝ)) := by
    intro t ht
    exact hK t ⟨by linarith [ht.1, hT_mid_lt_out], by linarith [ht.2, hT_mid_lt_out]⟩
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω := by
    apply hembed (ρ : ℝ) T
    · exact le_trans hρ_le_cap hρcap_le_ρa
    · exact le_trans hT_le_cap hTcap_le_Ta
  have hcontain₁ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1 ∈ closedBall x₀ (r : ℝ) := by
    intro x hx s hs
    have hx' : x ∈ closedBall x₀ ρ_c1 :=
      closedBall_subset_closedBall (le_trans hρ_le_cap hρcap_le_ρc1) hx
    have hs' : s ∈ Ioo (t₀ - T_c1) (t₀ + T_c1) :=
      ⟨by linarith [hs.1, hTmid_le_Tc1], by linarith [hs.2, hTmid_le_Tc1]⟩
    exact hcontain_aug x hx' s hs'
  have hcontain₂ : ∀ x ∈ closedBall x₀ (ρ : ℝ), ∀ s ∈ Ioo (t₀ - T_mid) (t₀ + T_mid),
      Φ ⟨x, s⟩ ∈ closedBall x₀ (r : ℝ) := by
    intro x hx s hs
    have hx' : x ∈ closedBall x₀ ρ_c2 :=
      closedBall_subset_closedBall (le_trans hρ_le_cap hρcap_le_ρc2) hx
    have hTmid_le_Tc2 : T_mid ≤ T_c2 := le_trans hTmid_le_cap hTcap_le_Tc2
    have hs' : s ∈ Ioo (t₀ - T_c2) (t₀ + T_c2) :=
      ⟨by linarith [hs.1, hTmid_le_Tc2], by linarith [hs.2, hTmid_le_Tc2]⟩
    exact hcontain_Φ x hx' s hs'
  have hbox_sub : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T) ⊆ U := by
    refine subset_trans ?_ hbox_p
    apply Set.prod_mono
    · exact ball_subset_ball (le_trans hρ_le_cap hρcap_le_ρp)
    · exact Ioo_subset_Ioo (by linarith [hT_le_cap, hTcap_le_Tp])
        (by linarith [hT_le_cap, hTcap_le_Tp])
  have hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    hU_Ck.mono hbox_sub
  have hfinal : ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_succ_via_augFlow hΦ haΦ haΦ_Ck hf_succ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
      hT_lt_mid (le_of_lt hT_mid_lt_out) hsub_out hsub' hsubO' hLip hr' hρ_lt_mid hρ_mid_lt_out
      hρρ' hρ_out_le_r hρR hmap hcontain₁ hcontain₂ hA_bd hΦ_Ck
  refine ⟨(ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T), isOpen_ball.prod isOpen_Ioo, ?_, hfinal⟩
  exact ⟨mem_ball_self hρ_pos, by constructor <;> linarith⟩

end CkDriver

section CkInduction

universe u

def FlowCkPred (n : ℕ) : Prop :=
  ∀ {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [FiniteDimensional ℝ E'] {g : ℝ → E' → E'} {t₀ : ℝ} {x₀ : E'} {r : ℝ≥0}
    {tmin tmax : ℝ} {Ψ : E' × ℝ → E'},
    IsLocalFlow g t₀ x₀ r tmin tmax Ψ →
    ContDiffOn ℝ (n : ℕ∞) (uncurry g) (Set.univ : Set (ℝ × E')) →
    t₀ ∈ Ioo tmin tmax → 0 < (r : ℝ) →
    ∃ U : Set (E' × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (n : ℕ∞) Ψ U

theorem flowCkPred_base : FlowCkPred.{u} 1 := by
  intro E' _ _ _ _ g t₀ x₀ r tmin tmax Ψ hΨ hg ht₀ hr
  have hg1 : ContDiffOn ℝ 1 (uncurry g) (Set.univ : Set (ℝ × E')) := by simpa using hg
  exact exists_contDiffOn_flow_C1 hΨ hg1 ht₀ hr

theorem flowCkPred_step {n : ℕ} (hn : 1 ≤ n) (IH : FlowCkPred.{u} n) :
    FlowCkPred.{u} (n + 1) := by
  intro E' _ _ _ _ g t₀ x₀ r tmin tmax Ψ hΨ hg ht₀ hr
  have horder : ((((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞)) =
      (((n : ℕ∞) : WithTop ℕ∞) + 1) := by norm_num
  have hg_succ : ContDiffOn ℝ ((n : ℕ∞) + 1) (uncurry g) (Set.univ : Set (ℝ × E')) := by
    rw [← horder]
    exact hg
  have h_augVF_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry (augmentedVectorField g))
      (Set.univ : Set (ℝ × (E' × (E' →L[ℝ] E')))) :=
    augVF_uncurry_contDiff (k := (n : ℕ∞)) hg_succ
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augmentedVectorField g))
      (Set.univ : Set (ℝ × (E' × (E' →L[ℝ] E')))) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
      have : (1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hn
      exact_mod_cast this
    simpa using h_augVF_Cn.of_le h_le
  obtain ⟨R, ε, hR_pos, hε_pos, aΨ, haΨ⟩ :=
    exists_isLocalFlow_of_contDiffOn_univ (augmentedVectorField g) h_augVF_C1 t₀
      (x₀, ContinuousLinearMap.id ℝ E')
  have ht₀_aug : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨Ω, hΩ_open, hΩ_mem, haΨ_Cn⟩ := IH haΨ h_augVF_Cn ht₀_aug hR_pos
  have hg_Cn : ContDiffOn ℝ (n : ℕ∞) (uncurry g) (Set.univ : Set (ℝ × E')) := by
    have h_le : ((n : ℕ∞) : WithTop ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
      have : (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ n
      exact_mod_cast this
    exact hg.of_le h_le
  have hΨ_prev := IH hΨ hg_Cn ht₀ hr
  obtain ⟨U, hU_open, hU_mem, hU_C⟩ := exists_contDiffOn_flow_succ_driver hΨ haΨ ht₀_aug hR_pos
    haΨ_Cn hΩ_open hΩ_mem hg_succ ht₀ hr hΨ_prev
  refine ⟨U, hU_open, hU_mem, ?_⟩
  rw [horder]
  exact hU_C

theorem flowCkPred_all (n : ℕ) (hn : 1 ≤ n) : FlowCkPred.{u} n := by
  induction n, hn using Nat.le_induction with
  | base => exact flowCkPred_base
  | succ m hm IH => exact flowCkPred_step hm IH

section Headline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_contDiffOn_flow_Cnat
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ (n : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ (n : ℕ∞) Φ U :=
  flowCkPred_all n hn hΦ hf ht₀ hr

theorem exists_contDiffOn_flow_C2
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ)) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ 2 Φ U := by
  obtain ⟨U, hU1, hU2, hU3⟩ :=
    exists_contDiffOn_flow_Cnat hΦ (n := 2) (by norm_num) (by exact_mod_cast hf) ht₀ hr
  exact ⟨U, hU1, hU2, by exact_mod_cast hU3⟩

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_flow_infty_of_spatial_smooth_all
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
    (hf_Cinfty : ContDiffOn ℝ ∞ (uncurry f) (Set.univ : Set (ℝ × E)))
    (hLsp_smooth : ∀ j : ℕ,
      ContDiffOn ℝ (j : ℕ∞) (spatialPieceFn Φ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ContDiffOn ℝ ∞ Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))
    simpa using hf_Cinfty.of_le h_le
  have hLsp_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (spatialPieceFn Φ q).coprod (timePieceFn f Φ q) :=
    fderiv_flow_eq_coprod_spatialPiece hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hA_bd
  rw [contDiffOn_infty]
  intro k
  have hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
    exact hf_Cinfty.of_le h_le
  exact contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck (fun _ => spatialPieceFn Φ)
    (fun j _ => hLsp_smooth j) (fun _ _ => hLsp_eq)

theorem exists_contDiffOn_flow_Cinfty
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiffOn ℝ ∞ (uncurry f) (Set.univ : Set (ℝ × E)))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hr : 0 < (r : ℝ))
    (hLsp : ∀ ⦃ρ : ℝ≥0⦄ ⦃T : ℝ⦄, 0 < T →
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T) ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax) →
      ∀ j : ℕ, ContDiffOn ℝ (j : ℕ∞) (spatialPieceFn Φ)
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x₀, t₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U := by
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))
    simpa using hf.of_le h_le
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ := exists_flow_nesting_data hΦ hf_C1 ht₀ hr
  have h_ρ_r : (ρ : ℝ) ≤ (r : ℝ) :=
    le_trans (le_of_lt hρ_lt_mid) (le_trans (le_of_lt hρ_mid_lt_out) hρ_out_le_r)
  have h_T_out : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T_out) (t₀ + T_out) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hbox_sub : (ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)
      ⊆ closedBall x₀ (r : ℝ) ×ˢ Icc tmin tmax := by
    intro q hq
    refine ⟨?_, ?_⟩
    · exact closedBall_subset_closedBall h_ρ_r
        (mem_closedBall.mpr (le_of_lt (mem_ball.mp hq.1)))
    · exact hsub (h_T_out (Ioo_subset_Icc_self hq.2))
  refine ⟨(ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T), isOpen_ball.prod isOpen_Ioo,
    ⟨mem_ball_self hρ_pos, ⟨by linarith, by linarith⟩⟩, ?_⟩
  exact contDiffOn_flow_infty_of_spatial_smooth_all hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub
    hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf (hLsp hT hbox_sub)

end Headline

end CkInduction

end Poincare.ODE.LocalFlow

end
