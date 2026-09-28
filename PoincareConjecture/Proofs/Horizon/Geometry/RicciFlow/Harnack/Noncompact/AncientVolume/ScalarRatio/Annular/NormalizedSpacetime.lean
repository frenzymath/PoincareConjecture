import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.NormalizedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeCompactness














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow





theorem exists_normalized_annular_spacetime_limit
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
    ∃ K₀ S ρ : ℝ, 0 < K₀ ∧ 0 < S ∧ 0 < ρ ∧ ρ < S / 2 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt
        ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
      (∀ k s, s ≤ 0 → MetricComplete ((G k).metric s)) ∧
      (∀ k s, s ≤ 0 → ∀ x, ((G k).connection s).NonnegativeCurvatureOperator x) ∧
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ K₀) ∧
      (∀ k, ((G k).connection 0).scalarCurvature (q (σ k)) = 1) ∧
      (∀ k, (Φ k).source = Metric.ball 0 S ∧
        (Φ k).target = ((G k).metric 0).ball (q (σ k)) S ∧ Φ k 0 = q (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q (σ k))).symm (extChartAt (𝓡 n) (q (σ k)) (q (σ k)))
            (L₀ k v) (L₀ k w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q (σ k)) (Φ k w))
          (L₀ k).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q (σ k)) (Φ k w) = ENNReal.ofReal ‖w‖) ∧
      ∃ (gLimit : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (_D : LeviCivitaData gLimit) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 (S / 4) ∧ V ⊆ Metric.ball 0 ρ ∧
        (∀ v w, gLimit.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m gLimit.euclideanCoefficients) atTop E) ∧
        ∃ B : ℝ × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
          ContDiffOn ℝ ∞ B (Iic 0 ×ˢ Metric.closedBall 0 ρ) ∧
          (∀ x ∈ V, B (0, x) = gLimit.euclideanCoefficients x) ∧
          (∀ v w, B (0, 0) v w = inner ℝ v w) ∧
          (∀ m E, IsCompact E → E ⊆ Iic 0 ×ˢ Metric.closedBall 0 ρ → TendstoUniformlyOn
            (fun k => iteratedFDerivWithin ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                ((G k).metric z.1).pullbackCoefficients (Φ k) z.2)
              (Iic 0 ×ˢ Metric.closedBall 0 ρ))
            (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ Metric.closedBall 0 ρ)) atTop E) := by
  obtain ⟨K₀, S, hK₀, hS, σ₀, hσ₀, L₀, Φ, hcurv, hscalar, hcharts,
    gLimit, D, V, hVo, hzeroV, hVS, hnorm, hterminal⟩ :=
    F.exists_terminal_normalized_annular_metric_limit hC hcomplete hoperator hK hbound
      hκ hnoncollapse hn t₀ ht₀ p q hQ hd hA hCnonneg hratio hdecay
  let H := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (σ₀ k))) (hQ (σ₀ k)) t₀ ht₀
  have hcompleteH : ∀ k t, t ≤ 0 → MetricComplete ((H k).metric t) := by
    intro k t ht
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (σ₀ k)).le)).trans ht₀)
  have hoperatorH : ∀ k t, t ≤ 0 → ∀ x,
      ((H k).connection t).NonnegativeCurvatureOperator x := by
    intro k t ht x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (σ₀ k)).le)).trans ht₀) x
  obtain ⟨ρ, hρ, hρS, τ, hτ, B, hB, hjets⟩ :=
    exists_ancient_exponential_spacetime_coefficient_subsequence hC hK₀ hS H
      hcompleteH hoperatorH (fun k => q (σ₀ k)) hcurv L₀ Φ
      (fun k => (hcharts k).1) (fun k => (hcharts k).2.2.1)
      (fun k => (hcharts k).2.2.2.1) (fun k => (hcharts k).2.2.2.2.1)
      (fun k => (hcharts k).2.2.2.2.2.1) (fun k => (hcharts k).2.2.2.2.2.2)
  have hterminal' : ∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (((H (τ k)).metric 0).pullbackCoefficients (Φ (τ k))))
      (iteratedFDeriv ℝ m gLimit.euclideanCoefficients) atTop E := by
    intro m E hE hEV u hu
    exact hτ.tendsto_atTop.eventually (hterminal m E hE hEV u hu)
  let W : Set (EuclideanSpace ℝ (Fin n)) := V ∩ Metric.ball 0 ρ
  have hzeroW : 0 ∈ W := ⟨hzeroV, Metric.mem_ball_self hρ⟩
  have heq : ∀ x ∈ W, B (0, x) = gLimit.euclideanCoefficients x := by
    intro x hx
    have hpoint : (0, x) ∈ Iic (0 : ℝ) ×ˢ Metric.closedBall 0 ρ :=
      ⟨by simp, Metric.ball_subset_closedBall hx.2⟩
    have htimejet := hjets 0 {(0, x)} isCompact_singleton (singleton_subset_iff.mpr hpoint)
    have htimevalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn htimejet
    have htime : Tendsto
        (fun k => ((H (τ k)).metric 0).pullbackCoefficients (Φ (τ k)) x)
        atTop (𝓝 (B (0, x))) := by
      simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
        htimevalue.tendsto_at (mem_singleton (0, x))
    have hspacejet := hterminal' 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx.1)
    have hspacevalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hspacejet
    have hspace : Tendsto
        (fun k => ((H (τ k)).metric 0).pullbackCoefficients (Φ (τ k)) x)
        atTop (𝓝 (gLimit.euclideanCoefficients x)) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        hspacevalue.tendsto_at (mem_singleton x)
    exact tendsto_nhds_unique htime hspace
  refine ⟨K₀, S, ρ, hK₀, hS, hρ, hρS, fun k => σ₀ (τ k), hσ₀.comp hτ,
    fun k => L₀ (τ k), fun k => Φ (τ k), fun k => hcompleteH (τ k),
    fun k => hoperatorH (τ k), fun k => hcurv (τ k), fun k => hscalar (τ k),
    fun k => hcharts (τ k), gLimit, D, W, hVo.inter Metric.isOpen_ball,
    hzeroW, fun x hx => hVS hx.1, inter_subset_right, hnorm,
    (fun m E hE hEW => hterminal' m E hE (hEW.trans inter_subset_left)),
    B, hB, heq, ?_, hjets⟩
  intro v w
  exact (congrArg (fun T => T v w) (heq 0 hzeroW)).trans (hnorm v w)

end PoincareConjecture.RicciFlow
