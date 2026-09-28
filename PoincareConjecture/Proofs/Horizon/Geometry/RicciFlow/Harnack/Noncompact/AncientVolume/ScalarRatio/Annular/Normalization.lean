import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace Poincare.AncientVolume

private theorem exists_annular_radii (n : ℕ) {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ b r : ℝ, 0 < b ∧ 0 < r ∧ b + 2 * r < Real.sqrt A ∧
      (n : ℝ) ^ 2 * (C / b ^ 2) ≤ r⁻¹ ^ 2 := by
  let b := Real.sqrt A / 2
  have hb : 0 < b := by dsimp [b]; positivity
  let K := (n : ℝ) ^ 2 * (C / b ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨r, hr, hsmall⟩ := exists_between (show (0 : ℝ) <
    min (Real.sqrt A / 4) (1 / (Real.sqrt K + 1)) by positivity)
  have hprod : r * (Real.sqrt K + 1) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < Real.sqrt K + 1)).mp (lt_min_iff.mp hsmall).2
  have hroot : Real.sqrt K ≤ r⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  refine ⟨b, r, hb, hr, ?_, ?_⟩
  · dsimp [b]
    linarith [(lt_min_iff.mp hsmall).1]
  · have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg K) hroot 2
    simpa only [Real.sq_sqrt hK] using hsquare

end Poincare.AncientVolume

namespace PoincareConjecture.RicciFlow

theorem eventually_ancientRescaleAt_normal_chart_with_curvature_control
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
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L : ℝ} (hA : 0 < A) (hCnonneg : 0 ≤ C)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    ∃ B S : ℝ, 0 < B ∧ 0 < S ∧ ∀ᶠ i in atTop,
      let G := F.ancientRescaleAt ((F.connection t₀).scalarCurvature (q i)) (hQ i) t₀ ht₀
      (∀ s ≤ 0, ∀ x ∈ (G.metric 0).ball (q i) (2 * S),
        (G.connection s).curvatureTensorNorm x ≤ B) ∧
      ∃ L₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 S ∧ Φ.target = (G.metric 0).ball (q i) S ∧ Φ 0 = q i ∧
        (∀ a b, (G.metric 0).pullbackCoefficients (extChartAt (𝓡 n) (q i)).symm
          (extChartAt (𝓡 n) (q i) (q i)) (L₀ a) (L₀ b) = inner ℝ a b) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q i) (Φ w)) L₀.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S,
          (G.metric 0).IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S, (G.metric 0).edist (q i) (Φ w) = ENNReal.ofReal ‖w‖ := by
  obtain ⟨b, r, hb, hr, hmargin, hrcurv⟩ :=
    Poincare.AncientVolume.exists_annular_radii n hA hCnonneg
  let B := (n : ℝ) ^ 2 * (C / b ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨hS, hSr, hcharts⟩ := F.eventually_ancientRescaleAt_uniform_exponential_charts
    hC hcomplete hoperator hK hbound hκ hnoncollapse hn t₀ ht₀ p q hQ hd
    hCnonneg hb hr hratio hdecay hmargin hrcurv
  let S := RiemannianMetric.localInjectivityRadius n B r (κ * r ^ n)
  refine ⟨B + 1, S, by positivity, hS, ?_⟩
  have hcenters := (F.ancientRescaleAt_basepoint_edist_tendsto_of_finite_ratio
    t₀ ht₀ p q hQ hratio).eventually_const_lt hmargin
  have hcurvature := F.eventually_ancientRescaleAt_annular_curvature_control hC hcomplete
    hoperator hK hbound t₀ ht₀ p q hQ hd hb hratio hdecay
  filter_upwards [hcharts, hcenters, hcurvature] with i hi hcenter hcurv
  dsimp only at hi ⊢
  let G := F.ancientRescaleAt ((F.connection t₀).scalarCurvature (q i)) (hQ i) t₀ ht₀
  constructor
  · intro s hs x hx
    have hmargin' : b + 2 * S ≤ ((G.metric 0).edist p (q i)).toReal := by
      change b + 2 * r < ((G.metric 0).edist p (q i)).toReal at hcenter
      change S < r at hSr
      linarith
    exact (hcurv s hs x
      ((G.metric 0).radial_lower_bound_on_ball p (q i) hmargin' x hx).le).trans
        (by change B ≤ B + 1; linarith)
  · obtain ⟨L₀, Φ, hsource, htarget, hzero, horth, hderiv, hgeo, hdist⟩ := hi
    refine ⟨L₀, Φ, hsource, htarget, hzero, horth, hderiv, ?_, hdist⟩
    intro w hw t ht
    exact hgeo w ((Metric.ball_subset_ball hSr.le) hw) t
      ((Metric.ball_subset_ball hSr.le) ht)

end PoincareConjecture.RicciFlow
