import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularRigidity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialEikonal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

theorem smooth_hessian_on_of_minimizing_identity
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : LeviCivitaData g) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {ρ : ℝ}
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 ρ)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ))
    (hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) U →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2) :
    ∀ x ∈ U, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
      ∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w := by
  let e : U → EuclideanSpace ℝ (Fin n) := Subtype.val
  have he : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) U
  let gU := g.pullbackOfLocalDiffeomorph e he
  let DU : LeviCivitaData gU := gU.leviCivitaData
  have hid (x : U) : mfderiv (𝓡 n) (𝓡 n) e x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal U x
  have hmetric (x : U) (v w : EuclideanSpace ℝ (Fin n)) :
      gU.inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w := by
    change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      (mfderiv (𝓡 n) (𝓡 n) e x w) = _
    rw [hid]
    rfl
  have hquadU : ∀ (γ : ℝ → U) (ε : ℝ), 0 < ε →
      gU.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        gU.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2 := by
    intro γ ε hε hγ t ht
    have hγE := hγ.subtype_val_of_inner_eq hmetric isOpen_Ioo
    have hh := g.geodesic_quadratic_on_of_minimizing_segments f U hquad hε hγE
      (fun s _ => (γ s).property) t ht
    have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have hs := tangentNorm_subtype_curve_of_inner_eq hmetric
      ((hγ.contMDiffAt h0).mdifferentiableAt one_ne_zero)
    rw [← hs] at hh
    exact hh
  have hfU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x) :=
    gU.contMDiff_of_locally_lipschitz_geodesic_quadratic (fun x : U => f x)
      (Poincare.AncientVolume.ScalarRatio.locally_lipschitz_opens_of_lipschitzOn_closedBall
        U hU f hLip) hquadU
  intro x hx
  let y : U := ⟨x, hx⟩
  let c := extChartAt (𝓡 n) y
  have hcx : x ∈ c.target := mem_extChartAt_target y
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) y hcx).contMDiffAt
      (extChartAt_target_mem_nhds' hcx)
  have hlocal : (fun z => f (c.symm z : EuclideanSpace ℝ (Fin n))) =ᶠ[𝓝 x] f := by
    filter_upwards [extChartAt_target_mem_nhds' hcx] with z hz
    exact congrArg f (c.right_inv hz)
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x :=
    ((hfU (c.symm x)).comp x hc).congr_of_eventuallyEq hlocal.symm
  refine ⟨hf, ?_⟩
  intro v w
  have hh := DU.hessian_comp_of_metric_pullback D (he.contMDiff y)
    (Eventually.of_forall (fun z => by
      rw [hid z]
      exact ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)), rfl⟩))
    (Eventually.of_forall (fun _ _ _ => rfl)) hf v w
  rw [hid] at hh
  change DU.hessian (fun z : U => f z) y v w = D.hessian f x v w at hh
  rw [← hh, DU.hessian_eq_metric_of_geodesic_quadratic hfU hquadU, hmetric]

theorem exists_local_radial_model_of_rescaled_normal_charts
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (Dg : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : Dg.NonnegativeSectionalCurvature) (p : M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData h)
    (q : ℕ → M) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (hQzero : Tendsto Q atTop (𝓝 0))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S : ℝ} (hS : 0 < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (rescaledMetric g (Q k) (hQ k)).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (rescaledMetric g (Q k) (hQ k)).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) (hzeroV : 0 ∈ V)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => (rescaledMetric g (Q k) (hQ k)).pullbackCoefficients (Φ k))
        h.euclideanCoefficients atTop K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfzero : 0 < f 0)
    {ρ : ℝ} (hVρ : V ⊆ Metric.ball 0 ρ)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ))
    (hpotential : TendstoUniformlyOn
      (fun k x => ((rescaledMetric g (Q k) (hQ k)).edist p (Φ k x)).toReal ^ 2 / 2)
      f atTop V) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ V ∧
      ∀ x ∈ U, 0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
        (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = h.inner x v w) ∧
        h.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  have hscale : Tendsto (fun k => Real.sqrt (Q k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hQzero
  obtain ⟨W, hWo, hzeroW, hWV, _, hinterp⟩ :=
    g.exists_local_minimizing_identity_of_rescaled_normal_charts hc p
      (fun a b ha hb α β hα0 hβ0 hαmin hβmin =>
        g.toponogov_corresponding_side_of_edist_segments Dg hc hsec ha hb hα0 hβ0 hαmin hβmin)
      h q Q hQ hscale Φ hS hsource htarget hradial hV hzeroV hconv f hfzero hpotential
  let Wopen : Opens (EuclideanSpace ℝ (Fin n)) := ⟨W, hWo⟩
  have hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      h.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) Wopen →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        h.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * h.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (h.edist (γ 0) (γ 1)).toReal ^ 2 / 2 := by
    intro γ ε hε hγ hγW hmin t ht
    apply hinterp (γ 0) (hγW (by simp)) (γ t) (hγW ht) (γ 1) (hγW (by simp)) t ht
    · rw [hmin 0 (by simp) t ht, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), zero_sub, abs_neg, abs_of_nonneg ht.1]
    · rw [hmin t ht 1 (by simp), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonpos (by linarith [ht.2]), neg_sub]
  have hregular := h.smooth_hessian_on_of_minimizing_identity D Wopen f
    (hWV.trans hVρ) hLip hquad
  obtain ⟨U, hUo, hzeroU, hUW, heikonal⟩ :=
    exists_local_radial_eikonal_of_normal_chart_coefficients
      (fun k => rescaledMetric g (Q k) (hQ k))
      (fun k => metricComplete_rescaledMetric g (Q k) (hQ k) hc)
      h D p q Φ hS hsource htarget hradial hWo hzeroW
      (fun K hK hKW => hconv K hK (hKW.trans hWV)) f hfzero
      (fun x hx => (hregular x hx).1) (hpotential.mono hWV)
  refine ⟨U, hUo, hzeroU, hUW.trans hWV, ?_⟩
  intro x hx
  exact ⟨(heikonal x hx).1, (hregular x (hUW hx)).1,
    (hregular x (hUW hx)).2, (heikonal x hx).2⟩

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_flat_local_radial_model_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D : LeviCivitaData g) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ),
      0 ∈ U ∧ f 0 = 1 / 2 ∧ (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
      ∀ x ∈ U, 0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
        D.curvatureTensorNorm x = 0 ∧
        (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w) ∧
        g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x := by
  obtain ⟨q, Q, hQ, hQzero, _, S, hS, _, L₀, Φ, _, _, hcharts,
    g, D, V, hVo, _, _, hnorm, hjets, hflat, R, hR, _, hRV, C, f,
    hLip, hpotential, hf0, _⟩ :=
    F.exists_flat_annular_limit_with_radial_potential_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  have hsmallV : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ V :=
    (fun x hx => hRV (Metric.ball_subset_closedBall
      ((Metric.ball_subset_ball (by linarith : R / 2 ≤ R)) hx)))
  have hcoeff : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ Metric.ball 0 (R / 2) →
      TendstoUniformlyOn (fun k => (rescaledMetric (F.metric t₀) (Q k) (hQ k)).pullbackCoefficients
        (Φ k)) g.euclideanCoefficients atTop K := by
    intro E hE hEW
    have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
        (hjets 0 E hE (hEW.trans hsmallV))
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply, ancientRescaleAt_metric,
      zero_div, add_zero] using hh
  obtain ⟨W, hWo, hzeroW, hWV, hmodel⟩ :=
    (F.metric t₀).exists_local_radial_model_of_rescaled_normal_charts
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p g D q Q hQ hQzero Φ hS
      (fun k => (hcharts k).1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts k).2.1)
      (fun k => by simpa only [ancientRescaleAt_metric, zero_div, add_zero]
        using (hcharts k).2.2.2.2.2.2)
      Metric.isOpen_ball (Metric.mem_ball_self (by positivity : 0 < R / 2)) hcoeff
      f (by rw [hf0]; norm_num)
      (Subset.rfl : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ Metric.ball 0 (R / 2))
      hLip (by simpa only [ancientRescaleAt_metric, zero_div, add_zero] using
        hpotential.mono Metric.ball_subset_closedBall)
  refine ⟨g, D, ⟨W, hWo⟩, f, hzeroW, hf0, hnorm, ?_⟩
  intro x hx
  exact ⟨(hmodel x hx).1, (hmodel x hx).2.1, hflat x (hsmallV (hWV hx)),
    (hmodel x hx).2.2.1, (hmodel x hx).2.2.2⟩

end PoincareConjecture.RicciFlow
