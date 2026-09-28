import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Curvature

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_distance_normalized_flat_annular_limit
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
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k, 3 / 4 ≤ (((G k).metric 0).edist p (q (σ k))).toReal) ∧
      (∀ k s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ 5) ∧
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
      ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 (S / 4) ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m g.euclideanCoefficients) atTop E) ∧
        ∀ x ∈ V, D.curvatureTensorNorm x = 0 := by
  obtain ⟨S, hS, hSr, hevent⟩ := F.eventually_distance_normalized_charts_of_zero_ratio
    hC hcomplete hoperator hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let H := fun k => F.ancientRescaleAt (Q (k + N)) (hQ (k + N)) t₀ ht₀
  have hgood (k : ℕ) := hN (k + N) (by omega)
  choose L₀ Φ hsource htarget hzeroΦ horth hderiv hgeo hdist using
    (fun k => (hgood k).2.2)
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
      ((H k).connection t).curvatureTensorNorm x ≤ 5 := fun k => (hgood k).2.1
  obtain ⟨τ, hτ, g, D, V, hVo, hzeroV, hVS, hnorm, hjets⟩ :=
    exists_terminal_exponential_metric_subsequence hC (by norm_num : (0 : ℝ) < 5) hS
      (by positivity : 0 < S / 4) (by linarith : S / 4 < S / 2)
      H hcompleteH hoperatorH (fun k => q (k + N)) hcurvH
      L₀ Φ hsource hzeroΦ horth hderiv hgeo hdist
  let σ : ℕ → ℕ := fun k => τ k + N
  have hσ : StrictMono σ := fun i j hij => Nat.add_lt_add_right (hτ hij) N
  refine ⟨S, hS, hSr, σ, hσ, fun k => L₀ (τ k), fun k => Φ (τ k),
    (fun k => (hgood (τ k)).1), (fun k => hcurvH (τ k)),
    (fun k => ⟨hsource (τ k), htarget (τ k), hzeroΦ (τ k), horth (τ k),
      hderiv (τ k), hgeo (τ k), hdist (τ k)⟩),
    g, D, V, hVo, hzeroV, hVS, hnorm, hjets, ?_⟩
  intro x hx
  have hxS : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S :=
    (Metric.ball_subset_ball (by linarith : S / 4 ≤ S)) (hVS hx)
  have hlimit := D.tendsto_curvatureTensorNorm_of_partialDiffeomorph_metric_jets
    (fun k => (H (τ k)).metric 0) (fun k => (H (τ k)).connection 0)
    (fun k => Φ (τ k)) x (fun k => by rw [hsource]; exact hxS)
    (fun r _ => (hjets r {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
      (mem_singleton x))
  have hvanish : Tendsto (fun k => ((H (τ k)).connection 0).curvatureTensorNorm (Φ (τ k) x))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := (F.eventually_ancientRescaleAt_annular_curvature_lt_of_zero_ratio
      hC hcomplete hoperator hK hbound t₀ ht₀ p hzero Q hQ hQzero
      (by norm_num : (0 : ℝ) < 1 / 2) hε).filter_mono hσ.tendsto_atTop
    filter_upwards [hsmall] with k hk
    have hball : Φ (τ k) x ∈ ((H (τ k)).metric 0).ball (q (σ k)) (2 * S) := by
      have hm := (Φ (τ k)).map_source (by rw [hsource]; exact hxS)
      rw [htarget] at hm
      exact (fun z (hz : ((H (τ k)).metric 0).edist (q (σ k)) z < ENNReal.ofReal S) =>
        hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith : S ≤ 2 * S))) _ hm
    have hmargin : 1 / 2 + 2 * S ≤ (((H (τ k)).metric 0).edist p (q (σ k))).toReal := by
      have hh := (hgood (τ k)).1
      change 3 / 4 ≤ (((H (τ k)).metric 0).edist p (q (σ k))).toReal at hh
      linarith
    have houter := ((H (τ k)).metric 0).radial_lower_bound_on_ball p (q (σ k))
      hmargin (Φ (τ k) x) hball
    have hb := hk 0 le_rfl (Φ (τ k) x) houter.le
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (show 0 ≤ ((H (τ k)).connection 0).curvatureTensorNorm (Φ (τ k) x) from
        Real.sqrt_nonneg _)] using hb
  exact tendsto_nhds_unique hlimit hvanish

end PoincareConjecture.RicciFlow
