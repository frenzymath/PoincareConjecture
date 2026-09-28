import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.ScalarFlow








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem hasDerivAt_potential_along_gradient_flow
    (S : GradientShrinkingSolitonData 3 M)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (S.connection.gradient S.potential)) (t : ℝ) :
    HasDerivAt (S.potential ∘ γ)
      (S.metric.inner (γ t) (S.connection.gradient S.potential (γ t))
        (S.connection.gradient S.potential (γ t))) t := by
  have h := RiemannianMetric.hasDerivAt_comp_integralCurve S.potential_contMDiff hγ t
  rw [S.connection.inner_gradient]
  exact h

theorem potential_monotone_on_gradient_flow
    (S : GradientShrinkingSolitonData 3 M)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (S.connection.gradient S.potential)) :
    Monotone (S.potential ∘ γ) := by
  apply monotone_of_hasDerivAt_nonneg (S.hasDerivAt_potential_along_gradient_flow hγ)
  intro t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  change 0 ≤ inner ℝ (S.connection.gradient S.potential (γ t))
    (S.connection.gradient S.potential (γ t))
  exact real_inner_self_nonneg



theorem potential_linear_growth_on_forward_gradient_curve
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a ≤ S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (S.connection.gradient S.potential))
    (hstart : a ≤ S.potential (γ 0)) (t : ℝ) (ht : 0 ≤ t) :
    S.potential (γ 0) + t ≤ S.potential (γ t) := by
  have hd : Differentiable ℝ (S.potential ∘ γ) :=
    fun s => (S.hasDerivAt_potential_along_gradient_flow hγ s).differentiableAt
  have hbound := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn
    (C := (1 : ℝ)) (fun s hs => by
      rw [(S.hasDerivAt_potential_along_gradient_flow hγ s).deriv]
      exact ha _ (hstart.trans (S.potential_monotone_on_gradient_flow hγ (interior_subset hs))))
    0 (by simp) t ht ht
  dsimp only [Function.comp_def] at hbound
  linarith



theorem forward_gradient_curve_centers_escape
    (S : GradientShrinkingSolitonData 3 M) {a : ℝ}
    (ha : ∀ x : M, a ≤ S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (S.connection.gradient S.potential))
    (hstart : a ≤ S.potential (γ 0)) (p : M) :
    Tendsto (fun k : ℕ => (S.metric.edist p (γ k)).toReal) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  let K := {x : M | S.metric.edist p x ≤ ENNReal.ofReal R}
  have hK : IsCompact K := S.metric.isCompact_closedBall_of_metricComplete S.complete p R
  obtain ⟨B, hB⟩ := hK.bddAbove_image S.potential_C2.continuous.continuousOn
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
    (B - S.potential (γ 0))] with k hk
  by_contra hnot
  have hmem : γ (k : ℝ) ∈ K := by
    change S.metric.edist p (γ (k : ℝ)) ≤ ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal (S.metric.edist_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (lt_of_not_ge hnot).le
  have hupper := hB (mem_image_of_mem _ hmem)
  have hlower := S.potential_linear_growth_on_forward_gradient_curve ha hγ hstart
    (k : ℝ) (Nat.cast_nonneg k)
  linarith



theorem scalar_strictMonoOn_forward_gradient_curve
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v)
    {a : ℝ} (ha : ∀ x : M, a ≤ S.potential x → 1 ≤
      S.metric.inner x (S.connection.gradient S.potential x)
        (S.connection.gradient S.potential x))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (S.connection.gradient S.potential))
    (hstart : a ≤ S.potential (γ 0)) :
    StrictMonoOn (fun t => S.connection.scalarCurvature (γ t)) (Ici 0) := by
  have hd := S.hasDerivAt_scalar_along_gradient_flow hD hγ
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
  intro t ht
  rw [(hd t).deriv]
  apply mul_pos (by norm_num)
  apply hRic
  intro hzero
  have hg := ha _ (hstart.trans (S.potential_monotone_on_gradient_flow hγ
    (show 0 ≤ t from interior_subset ht)))
  simp [hzero] at hg
  norm_num at hg



theorem exists_threshold_scalar_lt_of_escaping_subsequence
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v)
    (p : M) {c : ℝ}
    (hlimit : ∀ q : ℕ → M,
      Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop →
      ∃ r : ℕ → ℕ, StrictMono r ∧
        Tendsto (fun k => S.connection.scalarCurvature (q (r k))) atTop (𝓝 c)) :
    ∃ a : ℝ, ∀ x : M, a ≤ S.potential x → S.connection.scalarCurvature x < c := by
  obtain ⟨a, ha⟩ := S.exists_gradient_sq_gt_on_superlevel hD 1
  obtain ⟨C, hC, hess⟩ := S.exists_hessian_quadratic_bound
  obtain ⟨Φ, h0, hΦ, -, -⟩ :=
    S.connection.exists_complete_gradientFlow_of_bounded_hessian S.complete
      S.potential_contMDiff hC hess
  refine ⟨a, fun x hx => ?_⟩
  have hstart : a ≤ S.potential (Φ 0 x) := by rwa [h0 x]
  have hescape := S.forward_gradient_curve_centers_escape
    (fun y hy => (ha y hy).le) (hΦ x) hstart p
  obtain ⟨r, hr, hlim⟩ := hlimit (fun k => Φ (k : ℝ) x) hescape
  have hmono := S.scalar_monotone_on_gradient_flow hD (hΦ x)
    (fun y v => (S.connection.ricci_bounds_of_nonnegative_curvatureOperator
      hD y (S.nonnegative_curvature y) v).1)
  have hle : S.connection.scalarCurvature (Φ 1 x) ≤ c := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [hr.tendsto_atTop.eventually_ge_atTop 1] with k hk
    exact hmono (by exact_mod_cast hk)
  have hstrict := S.scalar_strictMonoOn_forward_gradient_curve hD hRic
    (fun y hy => (ha y hy).le) (hΦ x) hstart
    (show (0 : ℝ) ∈ Ici 0 by norm_num) (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  dsimp only at hstrict
  rw [h0 x] at hstrict
  exact hstrict.trans_le hle

end PoincareConjecture.GradientShrinkingSolitonData
