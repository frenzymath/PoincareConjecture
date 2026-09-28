import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.ScalarIdentity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.PotentialLevels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Generation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Flow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

noncomputable section

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem scalar_positive_of_ricci_positive
    (S : GradientShrinkingSolitonData 3 M)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v) :
    ∀ x : M, 0 < S.connection.scalarCurvature x := by
  intro x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  let b := S.metric.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    exact finrank_euclideanSpace_fin
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      b i ≠ 0 := by
    intro hz
    have hn := b.norm_eq_one i
    change ‖b i‖ = 1 at hn
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hsum : 0 < ∑ i, S.connection.ricci x (b i) (b i) := by
    apply Finset.sum_pos'
    · intro i hi
      exact (hRic x (b i) (hb i)).le
    · exact ⟨⟨0, by rw [hdim]; norm_num⟩, Finset.mem_univ _,
        hRic x (b ⟨0, by rw [hdim]; norm_num⟩)
          (hb ⟨0, by rw [hdim]; norm_num⟩)⟩
  simpa only [LeviCivitaData.scalarCurvature, b] using hsum

theorem hasDerivAt_scalar_along_gradient_flow
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ
      (S.connection.gradient S.potential)) (t : ℝ) :
    HasDerivAt (fun s => S.connection.scalarCurvature (γ s))
      (2 * S.connection.ricci (γ t)
        (S.connection.gradient S.potential (γ t))
        (S.connection.gradient S.potential (γ t))) t := by
  have hF := (S.connection.contMDiff_scalarCurvature (γ t)).mdifferentiableAt
    (by simp)
  have hcomp := hF.hasMFDerivAt.comp t (hγ t)
  have hder := (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).hasDerivAt
  change HasDerivAt (S.connection.scalarCurvature ∘ γ)
    (mvfderiv (𝓡 3) S.connection.scalarCurvature (γ t)
      ((1 : ℝ) • S.connection.gradient S.potential (γ t))) t at hder
  rw [one_smul, S.mvfderiv_scalarCurvature_threeDimensional hD] at hder
  simpa only [Function.comp_def] using hder

theorem scalar_monotone_on_gradient_flow
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ
      (S.connection.gradient S.potential))
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ S.connection.ricci x v v) :
    Monotone (fun t => S.connection.scalarCurvature (γ t)) := by
  have hdiff : ∀ t, DifferentiableAt ℝ
      (fun s => S.connection.scalarCurvature (γ s)) t := by
    intro t
    exact (S.hasDerivAt_scalar_along_gradient_flow hD hγ t).differentiableAt
  apply monotone_of_deriv_nonneg hdiff
  intro t
  rw [(S.hasDerivAt_scalar_along_gradient_flow hD hγ t).deriv]
  exact mul_nonneg (by norm_num) (hRic _ _)

theorem exists_potential_sublevel_on_backward_gradient_curve
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a ≤ S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ
      (S.connection.gradient S.potential)) :
    ∃ t : ℝ, t ≤ 0 ∧ S.potential (γ t) ≤ a := by
  have hd (t : ℝ) : HasDerivAt (S.potential ∘ γ)
      (S.metric.inner (γ t) (S.connection.gradient S.potential (γ t))
        (S.connection.gradient S.potential (γ t))) t := by
    have h := RiemannianMetric.hasDerivAt_comp_integralCurve
      S.potential_contMDiff hγ t
    rw [S.connection.inner_gradient]
    exact h
  by_contra h
  have habove (t : ℝ) (ht : t ≤ 0) : a < S.potential (γ t) := by
    by_contra hn
    exact h ⟨t, ht, le_of_not_gt hn⟩
  let t : ℝ := -(S.potential (γ 0) - a + 1)
  have ht : t ≤ 0 := by dsimp [t]; linarith [habove 0 le_rfl]
  have hdiff : Differentiable ℝ (S.potential ∘ γ) := fun s => (hd s).differentiableAt
  have hbound := (convex_Iic (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (C := (1 : ℝ)) (fun s hs => by
      rw [(hd s).deriv]
      exact ha (γ s) (habove s (show s ∈ Iic (0 : ℝ) from interior_subset hs)).le)
    t ht 0 (by simp) ht
  dsimp only [Function.comp_def] at hbound
  dsimp [t] at hbound
  linarith [habove t ht]

theorem exists_scalar_positive_global_lower_bound
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    (hR : ∀ x : M, 0 < S.connection.scalarCurvature x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, c ≤ S.connection.scalarCurvature x := by
  obtain ⟨a, ha⟩ := S.exists_gradient_sq_gt_on_superlevel hD 1
  obtain ⟨p, hp⟩ := S.exists_potential_minimum
  let b := max a (S.potential p)
  have hcore : ({x : M | S.potential x ≤ b}).Nonempty :=
    ⟨p, show S.potential p ≤ max a (S.potential p) from le_max_right _ _⟩
  have hcont : Continuous S.connection.scalarCurvature :=
    (show ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ S.connection.scalarCurvature from
      S.connection.contMDiff_scalarCurvature).continuous
  obtain ⟨q, hq, hmin⟩ := (S.isCompact_potential_sublevel b).exists_isMinOn
    hcore hcont.continuousOn
  refine ⟨S.connection.scalarCurvature q, hR q, ?_⟩
  obtain ⟨C, hC, hess⟩ := S.exists_hessian_quadratic_bound
  obtain ⟨Φ, h0, hΦ, -, -⟩ :=
    S.connection.exists_complete_gradientFlow_of_bounded_hessian S.complete
      S.potential_contMDiff hC hess
  intro x
  obtain ⟨t, ht, htx⟩ := S.exists_potential_sublevel_on_backward_gradient_curve
    (a := b) (fun y hy => (ha y ((le_max_left _ _).trans hy)).le) (hΦ x)
  have hmono := S.scalar_monotone_on_gradient_flow hD (hΦ x)
    (fun y v => (S.connection.ricci_bounds_of_nonnegative_curvatureOperator
      hD y (S.nonnegative_curvature y) v).1)
  have hx : S.connection.scalarCurvature (Φ t x) ≤
      S.connection.scalarCurvature (Φ 0 x) := hmono ht
  rw [h0 x] at hx
  exact (hmin htx).trans hx

end PoincareConjecture.GradientShrinkingSolitonData
