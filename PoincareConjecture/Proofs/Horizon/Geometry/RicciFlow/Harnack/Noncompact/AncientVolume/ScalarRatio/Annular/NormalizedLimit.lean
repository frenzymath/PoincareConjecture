import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.LimitMetric

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_terminal_normalized_annular_metric_limit
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
    ∃ B S : ℝ, 0 < B ∧ 0 < S ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt
        ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ B) ∧
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
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 (S / 4) ∧
        (∀ v w, gLimit.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m gLimit.euclideanCoefficients) atTop E) := by
  obtain ⟨B, S, hB, hS, hevent⟩ :=
    F.eventually_ancientRescaleAt_normal_chart_with_curvature_control hC hcomplete
      hoperator hK hbound hκ hnoncollapse hn t₀ ht₀ p q hQ hd hA hCnonneg hratio hdecay
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let H := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (k + N))) (hQ (k + N)) t₀ ht₀
  have hgood (k : ℕ) := hN (k + N) (by omega)
  choose L₀ Φ hsource htarget hzero horth hderiv hgeo hdist using
    (fun k => (hgood k).2)
  have hcompleteH : ∀ k t, t ≤ 0 → MetricComplete ((H k).metric t) := by
    intro k t ht
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (k + N)).le)).trans ht₀)
  have hoperatorH : ∀ k t, t ≤ 0 → ∀ x,
      ((H k).connection t).NonnegativeCurvatureOperator x := by
    intro k t ht x
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ ((add_le_of_nonpos_right
      (div_nonpos_of_nonpos_of_nonneg ht (hQ (k + N)).le)).trans ht₀) x
  have hcurvH : ∀ k t, t ≤ 0 → ∀ x ∈ ((H k).metric 0).ball (q (k + N)) (2 * S),
      ((H k).connection t).curvatureTensorNorm x ≤ B := fun k => (hgood k).1
  obtain ⟨τ, hτ, gLimit, D, V, hVo, hzeroV, hVS, hnorm, hjets⟩ :=
    exists_terminal_exponential_metric_subsequence hC hB hS
      (by positivity : 0 < S / 4) (by linarith : S / 4 < S / 2)
      H hcompleteH hoperatorH (fun k => q (k + N)) hcurvH
      L₀ Φ hsource hzero horth hderiv hgeo hdist
  refine ⟨B, S, hB, hS, fun k => τ k + N, ?_,
    fun k => L₀ (τ k), fun k => Φ (τ k), ?_, ?_, ?_,
    gLimit, D, V, hVo, hzeroV, hVS, hnorm, hjets⟩
  · exact fun i j hij => Nat.add_lt_add_right (hτ hij) N
  · exact fun k => hcurvH (τ k)
  · intro k
    exact F.ancientRescaleAt_scalarCurvature_zero _ (hQ (τ k + N)) t₀ ht₀ _ rfl
  · exact fun k => ⟨hsource (τ k), htarget (τ k), hzero (τ k), horth (τ k),
      hderiv (τ k), hgeo (τ k), hdist (τ k)⟩

end PoincareConjecture.RicciFlow
