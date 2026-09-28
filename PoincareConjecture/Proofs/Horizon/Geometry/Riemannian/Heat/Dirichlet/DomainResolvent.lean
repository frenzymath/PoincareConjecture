import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Density









set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem norm_toDomainL2_le (u : H1Zero D Ω) : ‖toDomainL2 D Ω u‖ ≤ ‖u‖ :=
  (norm_Lp_toLp_restrict_le Ω (toL2 D Ω u)).trans (norm_toL2_le u)

theorem inner_toDomainL2 (hΩ : MeasurableSet Ω) (u v : H1Zero D Ω) :
    ⟪toDomainL2 D Ω u, toDomainL2 D Ω v⟫_ℝ = ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ := by
  simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← map_sub, norm_toDomainL2 hΩ]


def domainResolvent (D : LeviCivitaData g) (Ω : Set M) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] H1Zero D Ω :=
  (toDomainL2 D Ω).adjoint

theorem domainResolvent_inner (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω))
    (u : H1Zero D Ω) :
    ⟪domainResolvent D Ω f, u⟫_ℝ = ⟪f, toDomainL2 D Ω u⟫_ℝ :=
  (toDomainL2 D Ω).adjoint_inner_left u f

theorem inner_restrict_toDomainL2 (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 g.volumeMeasure) (u : H1Zero D Ω) :
    ⟪LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω f, toDomainL2 D Ω u⟫_ℝ =
      ⟪f, toL2 D Ω u⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in Ω, inner ℝ (f x) (toL2 D Ω u x) ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [LpToLpRestrictCLM_coeFn ℝ Ω f, toDomainL2_ae u] with x hx hy
      rw [hx, hy]
    _ = _ := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [toL2_ae_zero_outside hΩ u] with x hx
      intro hxΩ
      rw [hx hxΩ, inner_zero_right]


theorem domainResolvent_restrict (hΩ : MeasurableSet Ω) (f : Lp ℝ 2 g.volumeMeasure) :
    domainResolvent D Ω (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω f) =
      resolvent D Ω f := by
  apply ext_inner_right ℝ
  intro u
  rw [domainResolvent_inner, resolvent_inner, inner_restrict_toDomainL2 hΩ]

theorem norm_domainResolvent_le : ‖domainResolvent D Ω‖ ≤ 1 := by
  change ‖(toDomainL2 D Ω).adjoint‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map]
  exact (toDomainL2 D Ω).opNorm_le_bound zero_le_one
    (fun u => by simpa using norm_toDomainL2_le u)

theorem domainResolvent_injective (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω)) :
    Function.Injective (domainResolvent D Ω) := by
  suffices hzero : ∀ f, domainResolvent D Ω f = 0 → f = 0 from
    fun f h heq => sub_eq_zero.mp (hzero (f - h) (by simpa using sub_eq_zero.mpr heq))
  intro f hf
  apply eq_zero_of_inner_toDomainL2_test_eq_zero (D := D) hΩ hcompact
  intro φ
  rw [← domainResolvent_inner, hf, inner_zero_left]


def domainL2Resolvent (D : LeviCivitaData g) (Ω : Set M) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  (toDomainL2 D Ω).comp (domainResolvent D Ω)

theorem domainL2Resolvent_inner (f h : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ⟪domainL2Resolvent D Ω f, h⟫_ℝ =
      ⟪domainResolvent D Ω f, domainResolvent D Ω h⟫_ℝ :=
  ((toDomainL2 D Ω).adjoint_inner_right (domainResolvent D Ω f) h).symm

theorem domainL2Resolvent_isSelfAdjoint : IsSelfAdjoint (domainL2Resolvent D Ω) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [domainL2Resolvent, domainResolvent, ContinuousLinearMap.adjoint_comp]

theorem norm_domainL2Resolvent_le (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ‖domainL2Resolvent D Ω f‖ ≤ ‖f‖ := by
  exact (norm_toDomainL2_le _).trans
    ((domainResolvent D Ω).le_of_opNorm_le norm_domainResolvent_le f |>.trans_eq (one_mul _))

theorem domainL2Resolvent_pos (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω))
    {f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)} (hf : f ≠ 0) :
    0 < ⟪domainL2Resolvent D Ω f, f⟫_ℝ := by
  rw [domainL2Resolvent_inner, real_inner_self_pos]
  intro hzero
  exact hf ((domainResolvent_injective hΩ hcompact)
    (hzero.trans (map_zero _).symm))

theorem domainL2Resolvent_injective (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω)) :
    Function.Injective (domainL2Resolvent D Ω) :=
  (toDomainL2 D Ω).self_comp_adjoint_injective_iff.mpr
    (domainResolvent_injective hΩ hcompact)

theorem denseRange_domainL2Resolvent (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω)) :
    DenseRange (domainL2Resolvent D Ω) := by
  change Dense (↑(domainL2Resolvent D Ω).range : Set (Lp ℝ 2 (g.volumeMeasure.restrict Ω)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.IsStarNormal.orthogonal_range
      (domainL2Resolvent_isSelfAdjoint (D := D) (Ω := Ω)).isStarNormal]
  exact LinearMap.ker_eq_bot.mpr (domainL2Resolvent_injective hΩ hcompact)

end PoincareConjecture.LeviCivitaData.Dirichlet
