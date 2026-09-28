import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.FlatChartFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric



theorem tendstoUniformlyOn_distance_of_normal_chart_uniform_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M]
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S r : ℝ} (hr : 0 < r) (hrS : r < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ h.tangentNorm x v ∧ h.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (hconv : TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
      h.euclideanCoefficients atTop (Metric.closedBall 0 r)) :
    TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((g k).edist (Φ k z.1) (Φ k z.2)).toReal)
      (fun z => (h.edist z.1 z.2).toReal) atTop
      (Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20)) := by
  let s := r / 10
  have hs : 0 < s := by dsimp [s]; positivity
  have h3s : 3 * s < r := by dsimp [s]; linarith
  have hlimitBall : h.ball 0 (3 * s) ⊆ Metric.closedBall 0 r := by
    intro x hx
    have hlow := (h.edist_bounds_of_uniform_tangentNorm_bounds hbound 0 x).1.trans_lt hx
    have hnorm : ‖x‖ / 2 < 3 * s := by
      simpa only [sub_zero] using
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hlow
    simp only [Metric.mem_closedBall, dist_zero_right]
    dsimp [s] at hnorm
    linarith
  have hsmall : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 20) ⊆
      Metric.ball 0 s ∩ h.ball 0 s := by
    intro x hx
    have hnorm : ‖x‖ ≤ r / 20 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    refine ⟨?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right]
      dsimp [s]
      linarith
    · have hupper := (h.edist_bounds_of_uniform_tangentNorm_bounds hbound 0 x).2
      simp only [sub_zero] at hupper
      apply hupper.trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff hs).mpr
      dsimp [s]
      linarith
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let C := 1 + min (1 / 2) (ε / (4 * s))
  have hC : 1 < C := by
    have hh : 0 < min (1 / 2 : ℝ) (ε / (4 * s)) := lt_min (by norm_num) (by positivity)
    dsimp [C]
    linarith
  have herror : (C - 1) * (2 * s) < ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * s)).mp
      (min_le_right (1 / 2 : ℝ) (ε / (4 * s)))
    dsimp [C]
    nlinarith
  filter_upwards [eventually_normal_chart_tangent_bounds g h Φ
    (isCompact_closedBall _ _) hconv hC] with k hk z hz
  have hx := hsmall hz.1
  have hy := hsmall hz.2
  obtain ⟨hforward, hback⟩ := normal_chart_edist_bounds (g k) h (q k) (Φ k)
    hs (zero_lt_one.trans hC) hrS.le h3s (hsource k) (htarget k)
    (hradial k) hlimitBall hk hrS hx hy
  have hforward' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.edist_ne_top z.1 z.2)) hforward
  have hback' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((g k).edist_ne_top (Φ k z.1) (Φ k z.2))) hback
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_lt_one.trans hC).le] at hforward' hback'
  have hlimit : (h.edist z.1 z.2).toReal < 2 * s := by
    have hx' : (h.edist 0 z.1).toReal < s :=
      (ENNReal.lt_ofReal_iff_toReal_lt (h.edist_ne_top 0 z.1)).mp hx.2
    have hy' : (h.edist 0 z.2).toReal < s :=
      (ENNReal.lt_ofReal_iff_toReal_lt (h.edist_ne_top 0 z.2)).mp hy.2
    have ht := @dist_triangle _ h.toMetricSpace.toPseudoMetricSpace z.1 0 z.2
    rw [@dist_comm _ h.toMetricSpace.toPseudoMetricSpace z.1 0] at ht
    change (h.edist z.1 z.2).toReal ≤ (h.edist 0 z.1).toReal + (h.edist 0 z.2).toReal at ht
    linarith
  change |(h.edist z.1 z.2).toReal - ((g k).edist (Φ k z.1) (Φ k z.2)).toReal| < ε
  have hprod := mul_le_mul_of_nonneg_left hlimit.le (sub_pos.mpr hC).le
  apply abs_lt.mpr
  constructor
  · nlinarith
  · by_cases hh : ((g k).edist (Φ k z.1) (Φ k z.2)).toReal ≤ (h.edist z.1 z.2).toReal
    · have hm := mul_le_mul_of_nonneg_left hh (sub_pos.mpr hC).le
      nlinarith
    · linarith

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow



theorem exists_common_flat_annular_metrics_with_source_distances_of_zero_ratio
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
    (q : ℕ → ℕ → M)
    (hcenter : ∀ j k, 3 / 4 ≤
      (((F.ancientRescaleAt (Q k) (hQ k) t₀ ht₀).metric 0).edist p (q j k)).toReal) :
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k j s, s ≤ 0 → ∀ x ∈ ((G k).metric 0).ball (q j (σ k)) (2 * S),
        ((G k).connection s).curvatureTensorNorm x ≤ 5) ∧
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = ((G k).metric 0).ball (q j (σ k)) S ∧
        Φ k j 0 = q j (σ k) ∧
        (∀ v w, ((G k).metric 0).pullbackCoefficients
          (extChartAt (𝓡 n) (q j (σ k))).symm
          (extChartAt (𝓡 n) (q j (σ k)) (q j (σ k)))
            (L₀ k j v) (L₀ k j w) = inner ℝ v w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) (q j (σ k)) (Φ k j w))
          (L₀ k j).toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 S, ((G k).metric 0).IsGeodesicOn
          (fun t => Φ k j (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 S}) ∧
        ∀ w ∈ Metric.ball 0 S,
          ((G k).metric 0).edist (q j (σ k)) (Φ k j w) = ENNReal.ofReal ‖w‖) ∧
      ∃ (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (D : ∀ j, LeviCivitaData (g j)) (r : ℝ),
        0 < r ∧ 2 * r < S / 4 ∧
        (∀ k j, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ∧
          ((G k).metric 0).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
        (∀ j v w, (g j).inner 0 v w = inner ℝ v w) ∧
        (∀ j (x v : EuclideanSpace ℝ (Fin n)), ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧
          (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
        (∀ j x v, (g j).inner x x v = inner ℝ x v) ∧
        (∀ j x, 2 * r ≤ ‖x‖ → (g j).euclideanCoefficients x = innerSL ℝ) ∧
        (∀ j m C, IsCompact C → C ⊆ Metric.closedBall 0 r → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k j)))
          (iteratedFDeriv ℝ m (g j).euclideanCoefficients) atTop C) ∧
        (∀ j x, x ∈ Metric.closedBall 0 r → (D j).curvatureTensorNorm x = 0) ∧
        ∀ j, TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k j z.1) (Φ k j z.2)).toReal)
          (fun z => ((g j).edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 (r / 20) ×ˢ Metric.closedBall 0 (r / 20)) := by
  obtain ⟨S, hS, hSsmall, σ, hσ, L₀, Φ, hcurv, hcharts, g, D, r, hr, hrS,
    hsourcebound, hcenterMetric, hgnorm, hgauss, houtside, hjets, hflat⟩ :=
      F.exists_common_flat_annular_metrics_of_zero_ratio hC hcomplete hoperator
        hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
  refine ⟨S, hS, hSsmall, σ, hσ, L₀, Φ, hcurv, hcharts, g, D, r, hr, hrS,
    hsourcebound, hcenterMetric, hgnorm, hgauss, houtside, hjets, hflat, ?_⟩
  intro j
  have hconv : TendstoUniformlyOn
      (fun k => ((G k).metric 0).pullbackCoefficients (Φ k j))
      (g j).euclideanCoefficients atTop (Metric.closedBall 0 r) := by
    have hjet := hjets j 0 (Metric.closedBall 0 r) (isCompact_closedBall _ _) Subset.rfl
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hvalue
  exact RiemannianMetric.tendstoUniformlyOn_distance_of_normal_chart_uniform_bounds
    (fun k => (G k).metric 0) (g j) (fun k => q j (σ k)) (fun k => Φ k j)
    hr (by linarith) (fun k => (hcharts k j).1) (fun k => (hcharts k j).2.1)
    (fun k => (hcharts k j).2.2.2.2.2.2) (hgnorm j) hconv

end PoincareConjecture.RicciFlow
