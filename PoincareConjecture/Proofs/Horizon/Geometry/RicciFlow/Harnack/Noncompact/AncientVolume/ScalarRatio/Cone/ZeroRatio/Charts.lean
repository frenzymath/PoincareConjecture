import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.ZeroRatioDecay

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem eventually_distance_normalized_charts_of_zero_ratio
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
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (Q : ℕ → ℝ) (hQ : ∀ i, 0 < Q i) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M)
    (hcenter : Tendsto (fun i => Real.sqrt (Q i) * ((F.metric t₀).edist p (q i)).toReal)
      atTop (𝓝 1)) :
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧ ∀ᶠ i in atTop,
      let G := F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀
      3 / 4 ≤ ((G.metric 0).edist p (q i)).toReal ∧
      (∀ s ≤ 0, ∀ x ∈ (G.metric 0).ball (q i) (2 * S),
        (G.connection s).curvatureTensorNorm x ≤ 5) ∧
      ∃ L₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 S ∧ Φ.target = (G.metric 0).ball (q i) S ∧ Φ 0 = q i ∧
        (∀ a b, (G.metric 0).pullbackCoefficients (extChartAt (𝓡 n) (q i)).symm
          (extChartAt (𝓡 n) (q i) (q i)) (L₀ a) (L₀ b) = inner ℝ a b) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q i) (Φ w)) L₀.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S,
          (G.metric 0).IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S, (G.metric 0).edist (q i) (Φ w) = ENNReal.ofReal ‖w‖ := by
  let A : ℝ := 1 / ((n : ℝ) ^ 2 + 1)
  let B : ℝ := (n : ℝ) ^ 2 * (A / (1 / 2) ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB4 : B ≤ 4 := by
    have heq : B = 4 * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1) := by
      dsimp [B, A]
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ 2 + 1)).mpr
    nlinarith
  obtain ⟨L, hdecay⟩ := hzero A hA
  let S := RiemannianMetric.localInjectivityRadius n B (1 / 8) (κ * (1 / 8) ^ n)
  have hS : 0 < S := RiemannianMetric.localInjectivityRadius_pos _ _ (by norm_num) _
  have hSr : S < 1 / 8 := RiemannianMetric.localInjectivityRadius_lt _ _ (by norm_num) _
  have hsmall : Tendsto (fun i => Real.sqrt (Q i) * L) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hQzero).mul_const L
  have hradial : Tendsto (fun i =>
      (((F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀).metric 0).edist p (q i)).toReal)
      atTop (𝓝 1) := by
    simpa only [ancientRescaleAt_edist_toReal_zero] using hcenter
  refine ⟨S, hS, hSr, ?_⟩
  filter_upwards [hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hradial.eventually_const_lt (by norm_num : (3 / 4 : ℝ) < 1)] with i hscale hrad
  let G := F.ancientRescaleAt (Q i) (hQ i) t₀ ht₀
  have hmargin : 1 / 2 + 2 * (1 / 8) ≤ ((G.metric 0).edist p (q i)).toReal := by
    change 3 / 4 < ((G.metric 0).edist p (q i)).toReal at hrad
    linarith
  have hrcurv : B ≤ ((1 / 8 : ℝ)⁻¹) ^ 2 := hB4.trans (by norm_num)
  obtain ⟨_, _, L₀, Φ, hsource, htarget, hzeroΦ, horth, hderiv, hgeo, hdist⟩ :=
    F.ancientRescaleAt_uniform_exponential_chart_of_quadratic_decay hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn (Q i) (hQ i) t₀ ht₀ p (q i) hA.le
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 8)
      hdecay hscale.le hmargin hrcurv
  refine ⟨hrad.le, ?_, L₀, Φ, hsource, htarget, hzeroΦ, horth, hderiv, ?_, hdist⟩
  · intro s hs x hx
    have hmarginS : 1 / 2 + 2 * S ≤ ((G.metric 0).edist p (q i)).toReal := by
      linarith
    exact (F.ancientRescaleAt_curvatureTensorNorm_le_of_quadratic_decay hC hcomplete
      hoperator hK hbound (Q i) (hQ i) t₀ ht₀ p (by norm_num : (0 : ℝ) < 1 / 2)
      hdecay hscale.le s hs x
      ((G.metric 0).radial_lower_bound_on_ball p (q i) hmarginS x hx).le).trans
        (hB4.trans (by norm_num))
  · intro w hw t ht
    exact hgeo w ((Metric.ball_subset_ball hSr.le) hw) t
      ((Metric.ball_subset_ball hSr.le) ht)

end PoincareConjecture.RicciFlow
