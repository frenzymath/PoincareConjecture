import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.RescaledBallControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem ancientRescaleAt_uniform_exponential_chart_of_scalar_bound
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
    (hn : 1 ≤ n) (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0)
    (a : ℝ) (ha : a ≤ 0) (q : M) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (hscalar : ∀ x ∈ ((F.ancientRescaleAt Q hQ t₀ ht₀).metric a).ball q (2 * r),
      ((F.ancientRescaleAt Q hQ t₀ ht₀).connection a).scalarCurvature x ≤ A)
    (hscale : (n : ℝ) ^ 2 * A ≤ r⁻¹ ^ 2) :
    let G := F.ancientRescaleAt Q hQ t₀ ht₀
    let ρ := RiemannianMetric.localInjectivityRadius n ((n : ℝ) ^ 2 * A) r (κ * r ^ n)
    0 < ρ ∧ ρ < r ∧
      (∀ s ≤ a, ∀ x ∈ (G.metric a).ball q (2 * r),
        (G.connection s).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * A) ∧
      ∃ L₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 ρ ∧ Φ.target = (G.metric a).ball q ρ ∧ Φ 0 = q ∧
        (∀ v w, (G.metric a).pullbackCoefficients (extChartAt (𝓡 n) q).symm
          (extChartAt (𝓡 n) q q) (L₀ v) (L₀ w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) q (Φ w)) L₀.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 r,
          (G.metric a).IsGeodesicOn (fun t => Φ (t • w))
            {t : ℝ | t • w ∈ Metric.ball 0 r}) ∧
        ∀ w ∈ Metric.ball 0 ρ, (G.metric a).edist q (Φ w) = ENNReal.ofReal ‖w‖ := by
  let G := F.ancientRescaleAt Q hQ t₀ ht₀
  have htime (s : ℝ) (hs : s ≤ 0) : t₀ + s / Q ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le)).trans ht₀
  have hpast : ∀ s ≤ a, ∀ x ∈ (G.metric a).ball q (2 * r),
      (G.connection s).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * A := by
    intro s hs x hx
    have hoperatorG : (G.connection s).NonnegativeCurvatureOperator x :=
      F.parabolicRescale_nonnegativeCurvatureOperator Q hQ t₀ _ _ _ s x
        (hoperator _ (htime s (hs.trans ha)) x)
    apply ((G.connection s).curvatureTensorNorm_le_scalarCurvature
      (hC.tensor_calculus n M (G.metric s) (G.connection s)) x hoperatorG).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply le_trans _ (hscalar x hx)
    rw [ancientRescaleAt_scalarCurvature, ancientRescaleAt_scalarCurvature]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hQ.le)
    exact F.scalarCurvature_monotoneOn_of_bounded_ancient hC hcomplete hoperator hK hbound x
      (htime s (hs.trans ha)) (htime a ha)
      (by linarith [div_le_div_of_nonneg_right hs hQ.le])
  have hcompleteG : MetricComplete (G.metric a) := by
    rw [ancientRescaleAt_metric]
    exact metricComplete_rescaledMetric _ Q hQ (hcomplete _ (htime a ha))
  have hcompact : IsCompact (closure ((G.metric a).ball q (2 * r))) := by
    let := (G.metric a).toMetricSpace
    let : ProperSpace M := (G.metric a).properSpace_toMetricSpace hcompleteG
    rw [← (G.metric a).toMetricSpace_ball]
    exact (isCompact_closedBall q (2 * r)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hvolume := F.ancientRescaleAt_volume_lower_bound_of_scalar_bound hC hcomplete
    hoperator hK hbound hnoncollapse Q hQ t₀ ht₀ a ha q hr
    (fun x hx => hscalar x (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))) hscale
  obtain ⟨hρ, hρr, hchart⟩ :=
    (G.metric a).exists_uniform_precompact_exponential_diffeomorph (G.connection a) q
      hn (mul_nonneg (sq_nonneg _) hA) hr (mul_pos hκ (pow_pos hr n))
      hcompact (hpast a le_rfl) hvolume
  exact ⟨hρ, hρr, hpast, hchart⟩

end PoincareConjecture.RicciFlow
