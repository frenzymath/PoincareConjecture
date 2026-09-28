import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_StandardGeodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

open M36 RiemannianMetric

noncomputable def standardRadialExponential (g₀ : StandardInitialMetric)
    (v : StandardCapSpace) : StandardCapSpace :=
  radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖) • (‖v‖⁻¹ • v)

noncomputable def standardRadialLogarithm (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : StandardCapSpace :=
  (radialArclength g₀ ‖x‖ / radialSpeed g₀ 0) • (‖x‖⁻¹ • x)

theorem standardRadialExponential_zero (g₀ : StandardInitialMetric) :
    standardRadialExponential g₀ 0 = 0 := by
  simp [standardRadialExponential]

theorem standardRadialLogarithm_zero (g₀ : StandardInitialMetric) :
    standardRadialLogarithm g₀ 0 = 0 := by
  simp [standardRadialLogarithm]

theorem norm_standardRadialExponential (g₀ : StandardInitialMetric)
    (v : StandardCapSpace) :
    ‖standardRadialExponential g₀ v‖ =
      radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [standardRadialExponential_zero, radialEuclideanRadius_zero]
  have hr : 0 < radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖) :=
    (radialEuclideanRadius_pos_iff g₀ _).mpr
      (mul_pos (radialSpeed_pos g₀ 0) (norm_pos_iff.mpr hv))
  simp [standardRadialExponential, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, norm_ne_zero_iff.mpr hv]

theorem norm_standardRadialLogarithm (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) :
    ‖standardRadialLogarithm g₀ x‖ = radialArclength g₀ ‖x‖ / radialSpeed g₀ 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [standardRadialLogarithm_zero, radialArclength_zero]
  have hr : 0 < radialArclength g₀ ‖x‖ / radialSpeed g₀ 0 :=
    div_pos (radialArclength_pos g₀ (norm_pos_iff.mpr hx)) (radialSpeed_pos g₀ 0)
  rw [standardRadialLogarithm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  simp [norm_smul, norm_ne_zero_iff.mpr hx]

theorem standardRadialLogarithm_exponential (g₀ : StandardInitialMetric)
    (v : StandardCapSpace) :
    standardRadialLogarithm g₀ (standardRadialExponential g₀ v) = v := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [standardRadialExponential_zero, standardRadialLogarithm_zero]
  have hvnorm := norm_ne_zero_iff.mpr hv
  have hr : radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖) ≠ 0 :=
    ((radialEuclideanRadius_pos_iff g₀ _).mpr
      (mul_pos (radialSpeed_pos g₀ 0) (norm_pos_iff.mpr hv))).ne'
  unfold standardRadialLogarithm
  rw [norm_standardRadialExponential, radialArclength_euclideanRadius,
    mul_div_cancel_left₀ _ (radialSpeed_pos g₀ 0).ne']
  simp only [standardRadialExponential, smul_smul]
  have hc : ‖v‖ *
      ((radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖))⁻¹ *
        (radialEuclideanRadius g₀ (radialSpeed g₀ 0 * ‖v‖) * ‖v‖⁻¹)) = 1 := by
    rw [inv_mul_cancel_left₀ hr, mul_inv_cancel₀ hvnorm]
  rw [hc, one_smul]

theorem standardRadialExponential_logarithm (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) :
    standardRadialExponential g₀ (standardRadialLogarithm g₀ x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [standardRadialLogarithm_zero, standardRadialExponential_zero]
  have hxnorm := norm_ne_zero_iff.mpr hx
  have hR := (radialArclength_pos g₀ (norm_pos_iff.mpr hx)).ne'
  have hc := (radialSpeed_pos g₀ 0).ne'
  unfold standardRadialExponential
  rw [norm_standardRadialLogarithm, mul_div_cancel₀ _ hc,
    radialEuclideanRadius_arclength]
  simp only [standardRadialLogarithm, smul_smul]
  have hs : ‖x‖ * ((radialArclength g₀ ‖x‖ / radialSpeed g₀ 0)⁻¹ *
      (radialArclength g₀ ‖x‖ / radialSpeed g₀ 0 * ‖x‖⁻¹)) = 1 := by
    field_simp
  rw [hs, one_smul]

theorem standardRadialExponential_injective (g₀ : StandardInitialMetric) :
    Function.Injective (standardRadialExponential g₀) := by
  have hleft : Function.LeftInverse (standardRadialLogarithm g₀)
      (standardRadialExponential g₀) := standardRadialLogarithm_exponential g₀
  exact hleft.injective

theorem exists_standard_radial_geodesic (g₀ : StandardInitialMetric)
    (v : StandardCapSpace) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → StandardCapSpace,
      g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = 0 ∧
      HasDerivAt γ v 0 ∧ γ 1 = standardRadialExponential g₀ v := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, zero_lt_one, fun _ => 0, g₀.metric.isGeodesicOn_const 0 _, rfl,
      hasDerivAt_const 0 0, (standardRadialExponential_zero g₀).symm⟩
  let x := standardRadialExponential g₀ v
  have hx : x ≠ 0 := by
    intro hz
    have h := standardRadialLogarithm_exponential g₀ v
    change standardRadialLogarithm g₀ x = v at h
    rw [hz, standardRadialLogarithm_zero] at h
    exact hv h.symm
  let R := radialArclength g₀ ‖x‖ + 1
  have hR : 0 < R := by
    dsimp only [R]
    linarith [standard_radial_arclength_nonneg g₀ x]
  have hcompact : IsCompact (closure (g₀.metric.ball 0 R)) := by
    rw [standard_closure_ball g₀ hR]
    exact standard_closed_ball_compact g₀ hR.le
  have hxball : x ∈ g₀.metric.ball 0 R := by
    change g₀.metric.edist 0 x < ENNReal.ofReal R
    rw [standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff hR]
    dsimp only [R]
    linarith
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g₀.metric.exists_minimizing_geodesic_of_precompact_ball 0 x hR hcompact hxball
  refine ⟨ε, hε, γ, hγ, hγ0, ?_, hγ1⟩
  have hd := standard_segment_initial_velocity g₀ hε hγ hγ0 hγ1 hx hmin
  change HasDerivAt γ (standardRadialLogarithm g₀ (standardRadialExponential g₀ v)) 0
    at hd
  simpa only [standardRadialLogarithm_exponential] using hd

theorem standard_exponential_eq_radial (g₀ : StandardInitialMetric)
    {e : StandardCapSpace → StandardCapSpace} {V : Set StandardCapSpace}
    (hexp : ∀ v ∈ V, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → StandardCapSpace,
      g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = 0 ∧
      HasDerivAt (fun t => extChartAt (𝓡 3) (0 : StandardCapSpace) (γ t)) v 0 ∧
      γ 1 = e v) :
    EqOn e (standardRadialExponential g₀) V := by
  intro v hv
  obtain ⟨ε, hε, γ, hγ, hγ0, hγv, hγ1⟩ := hexp v hv
  obtain ⟨δ, hδ, η, hη, hη0, hηv, hη1⟩ := exists_standard_radial_geodesic g₀ v
  have hηv' : HasDerivAt
      (fun t => extChartAt (𝓡 3) (0 : StandardCapSpace) (η t)) v 0 := by
    simpa only [StandardCapSpace, extChartAt_self_eq, modelWithCornersSelf_coe,
      id_eq] using hηv
  have hγ' : g₀.metric.IsGeodesicOn γ (Icc (0 : ℝ) 1) :=
    fun t ht => hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hη' : g₀.metric.IsGeodesicOn η (Icc (0 : ℝ) 1) :=
    fun t ht => hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact hγ1.symm.trans
    ((geodesic_endpoint_eq_of_initial_data hγ' hη' hγ0 hη0 hγv hηv').trans hη1)

end PoincareConjecture.M44
