import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartDistances
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnularEmbedding












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric



theorem exists_isometric_cone_limit_of_rescaled_normal_charts
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (D₀ : LeviCivitaData g₀)
    (hc : MetricComplete g₀) (hsec : D₀.NonnegativeSectionalCurvature) (p : M)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → M) (Φ : ℕ → EuclideanSpace ℝ (Fin n) → M)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hcenter : Tendsto
      (fun k => ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q k)).toReal)
      atTop (𝓝 1))
    (hradial : ∀ k x, x ∈ Metric.closedBall 0 r →
      (rescaledMetric g₀ (Q k) (hQ k)).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (hdist : TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k z.1) (Φ k z.2)).toReal)
      (fun z => (g.edist z.1 z.2).toReal) atTop
      (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r)) :
    let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
    letI metricA : MetricSpace A :=
      MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
    letI : PseudoEMetricSpace A :=
      @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
    letI := g₀.toMetricSpace
    let hcomparison := g₀.rayComparison_of_metricComplete D₀ hc hsec p
    let L := fun k => 1 / Real.sqrt (Q k)
    ∃ τ : ℕ → ℕ, Tendsto τ atTop atTop ∧
      (∀ k, 0 < L (τ k)) ∧
      (∀ k (x : A), Φ (τ k) x ∈ rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∃ ψ : ℕ → A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
          ∃ e : A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
            (∀ k (x : A), annulusConeRelation hcomparison (L (τ k))
              ((1 / ((k : ℝ) + 1)) / 4) (Φ (τ k) x) (ψ k x)) ∧
            (∀ k (x y : rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2)
              (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
              annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) x z →
              annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) y w →
              |(g₀.edist (x : M) (y : M)).toReal / L (τ k) - dist z w| <
                1 / ((k : ℝ) + 1)) ∧
            Isometry e ∧ TendstoUniformly ψ e (U : Filter ℕ) ∧
            ∀ z, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (ψ k x) z < ε) → z ∈ range e := by
  classical
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  have hcompact : IsCompact A := isCompact_closedBall _ _
  have hxnorm (x : A) : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ r := by
    simpa only [A, Metric.mem_closedBall, dist_zero_right] using x.property
  let metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
  let : PseudoEMetricSpace A :=
    @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
  let : CompactSpace A := isCompact_iff_compactSpace.mp hcompact
  let L := fun k => 1 / Real.sqrt (Q k)
  have hscale : Tendsto (fun k => Real.sqrt (Q k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hQzero
  have hL : Tendsto L atTop atTop := by
    simpa only [L, one_div, Function.comp_def] using
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hscale, Eventually.of_forall (fun k => Real.sqrt_pos.2 (hQ k))⟩)
  have hscaled (k : ℕ) (x y : M) :
      (g₀.edist x y).toReal / L k =
        ((rescaledMetric g₀ (Q k) (hQ k)).edist x y).toReal := by
    rw [rescaledMetric_edist, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    dsimp only [L]
    rw [div_div_eq_mul_div, div_one, mul_comm]
  have hrad : ∀ᶠ k in atTop, ∀ x : A,
      1 / 2 ≤ (g₀.edist p (Φ k x)).toReal / L k ∧
        (g₀.edist p (Φ k x)).toReal / L k ≤ 2 := by
    filter_upwards [hcenter.eventually (eventually_gt_nhds (by norm_num : (3 : ℝ) / 4 < 1)),
      hcenter.eventually_lt_const (by norm_num : (1 : ℝ) < 5 / 4)] with k hklo hkhi x
    rw [hscaled]
    have hxn := hxnorm x
    have hxrad := congrArg ENNReal.toReal (hradial k x x.property)
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hxrad
    let := (rescaledMetric g₀ (Q k) (hQ k)).toMetricSpace
    have hl := dist_triangle p (Φ k x) (q k)
    have hu := dist_triangle p (q k) (Φ k x)
    rw [dist_comm (Φ k x) (q k)] at hl
    change ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q k)).toReal ≤
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (Φ k x)).toReal +
      ((rescaledMetric g₀ (Q k) (hQ k)).edist (q k) (Φ k x)).toReal at hl
    change ((rescaledMetric g₀ (Q k) (hQ k)).edist p (Φ k x)).toReal ≤
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q k)).toReal +
      ((rescaledMetric g₀ (Q k) (hQ k)).edist (q k) (Φ k x)).toReal at hu
    constructor <;> linarith
  have hdistA : TendstoUniformly
      (fun k (z : A × A) => (g₀.edist (Φ k z.1) (Φ k z.2)).toReal / L k)
      (fun z => (g.edist z.1 z.2).toReal) atTop := by
    rw [Metric.tendstoUniformly_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hdist
    intro ε hε
    filter_upwards [hdist ε hε] with k hk z
    simpa only [hscaled] using hk (z.1, z.2) ⟨z.1.property, z.2.property⟩
  exact g₀.exists_isometric_cone_limit_of_annular_distance_convergence D₀ hc hsec p
    (by norm_num) (by norm_num) L hL (fun k (x : A) => Φ k x) hrad hdistA

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow





theorem exists_flat_radial_cone_embedding_along_ray_of_zero_ratio
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
    letI := (F.metric t₀).toMetricSpace
    ∀ η : basedMinimizingRays p,
    let q := fun k : ℕ => rayExtension η ((k : ℝ) + 1)
    let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
    let hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hcomparison := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    ∃ S : ℝ, 0 < S ∧ S < 1 / 8 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ L₀ : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      let G := fun k => F.ancientRescaleAt (Q (σ k)) (hQ (σ k)) t₀ ht₀
      (∀ k, (((G k).metric 0).edist p (q (σ k))).toReal = 1) ∧
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
        (D : LeviCivitaData g) (r : ℝ), 0 < r ∧ 2 * r < S ∧
        (∀ v w, g.inner 0 v w = inner ℝ v w) ∧
        (∀ m E, IsCompact E → E ⊆ Metric.closedBall 0 (2 * r) → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (((G k).metric 0).pullbackCoefficients (Φ k)))
          (iteratedFDeriv ℝ m g.euclideanCoefficients) atTop E) ∧
        TendstoUniformlyOn
          (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            (((G k).metric 0).edist (Φ k z.1) (Φ k z.2)).toReal)
          (fun z => (g.edist z.1 z.2).toReal) atTop
          (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r) ∧
        ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          LipschitzOnWith C f (Metric.closedBall 0 (2 * r)) ∧
          TendstoUniformlyOn
            (fun k x => (((G k).metric 0).edist p (Φ k x)).toReal ^ 2 / 2)
            f atTop (Metric.closedBall 0 (2 * r)) ∧ f 0 = 1 / 2 ∧
          (∀ x ∈ Metric.closedBall 0 (2 * r),
            0 < f x ∧ ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x ∧
              D.curvatureTensorNorm x = 0 ∧
              (∀ v w : EuclideanSpace ℝ (Fin n), D.hessian f x v w = g.inner x v w) ∧
              g.inner x (D.gradient f x) (D.gradient f x) = 2 * f x) ∧
          let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
          letI metricA : MetricSpace A :=
            MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
          letI : PseudoEMetricSpace A :=
            @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
          let L := fun k => 1 / Real.sqrt (Q (σ k))
          ∃ τ : ℕ → ℕ, Tendsto τ atTop atTop ∧
            (∀ k, 0 < L (τ k)) ∧
            (∀ k (x : A), Φ (τ k) x ∈ rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2) ∧
            ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
              ∃ ψ : ℕ → A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
                ∃ e : A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
                  (∀ k (x : A), annulusConeRelation hcomparison (L (τ k))
                    ((1 / ((k : ℝ) + 1)) / 4) (Φ (τ k) x) (ψ k x)) ∧
                  (∀ k (x y : M),
                    x ∈ rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2 →
                    y ∈ rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2 →
                    ∀ z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
                    annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) x z →
                    annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) y w →
                    |((F.metric t₀).edist (x : M) (y : M)).toReal / L (τ k) - dist z w| <
                      1 / ((k : ℝ) + 1)) ∧
                  Isometry e ∧ TendstoUniformly ψ e (U : Filter ℕ) ∧
                  ∀ z, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (ψ k x) z < ε) → z ∈ range e := by
  classical
  let := (F.metric t₀).toMetricSpace
  intro η
  let q := fun k : ℕ => rayExtension η ((k : ℝ) + 1)
  let Q := fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2
  have hQ : ∀ k, 0 < Q k := fun k => by dsimp [Q]; positivity
  have hQzero : Tendsto Q atTop (𝓝 0) := by
    simpa only [Q, one_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)).pow 2
  have hsqrt (k : ℕ) : Real.sqrt (Q k) = ((k : ℝ) + 1)⁻¹ := by
    exact Real.sqrt_sq (by positivity)
  have hd (k : ℕ) : ((F.metric t₀).edist p (q k)).toReal = (k : ℝ) + 1 := by
    change dist p (rayExtension η ((k : ℝ) + 1)) = (k : ℝ) + 1
    simpa only [rayExtension_zero, zero_sub, abs_neg,
      abs_of_pos (by positivity : 0 < (k : ℝ) + 1)] using
        rayExtension_dist η (s := 0) (t := (k : ℝ) + 1) (by norm_num) (by positivity)
  have hnormcenter (k : ℕ) :
      Real.sqrt (Q k) * ((F.metric t₀).edist p (q k)).toReal = 1 := by
    rw [hsqrt, hd, inv_mul_cancel₀ (by positivity : (k : ℝ) + 1 ≠ 0)]
  have hcenter : Tendsto
      (fun k => Real.sqrt (Q k) * ((F.metric t₀).edist p (q k)).toReal)
      atTop (𝓝 1) := by
    simpa only [hnormcenter] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  obtain ⟨S, hS, hSr, σ, hσ, L₀, Φ, _, hcenterG, hcurv, hcharts,
    g, D, r, hr, h2rS, hnorm, hjets, hdist, C, f, hLip, hpotential, hf0, hmodel⟩ :=
    F.exists_distance_normalized_flat_radial_chart_with_source_distances hC hcomplete hoperator
      hK hbound hκ hnoncollapse hn t₀ ht₀ p hzero Q hQ hQzero q hcenter
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  refine ⟨S, hS, hSr, σ, hσ, L₀, Φ, ?_, hcurv, hcharts, g, D, r, hr, h2rS,
    hnorm, hjets, hdist, C, f, hLip, hpotential, hf0, hmodel, ?_⟩
  · intro k
    rw [ancientRescaleAt_edist_toReal_zero]
    exact hnormcenter (σ k)
  · have hcenter' : Tendsto
        (fun k => ((rescaledMetric (F.metric t₀) (Q (σ k)) (hQ (σ k))).edist
          p (q (σ k))).toReal) atTop (𝓝 1) := by
      simpa only [ancientRescaleAt_metric, zero_div, add_zero] using hcenterG
    have hradial' : ∀ k x, x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r →
        (rescaledMetric (F.metric t₀) (Q (σ k)) (hQ (σ k))).edist
          (q (σ k)) (Φ k x) = ENNReal.ofReal ‖x‖ := by
      intro k x hx
      have hxS : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S :=
        Metric.closedBall_subset_ball (by linarith) hx
      simpa only [ancientRescaleAt_metric, zero_div, add_zero] using
        (hcharts k).2.2.2.2.2.2 x hxS
    obtain ⟨τ, hτ, hL, hsource, U, hU, ψ, e, hrel, hdistortion, he, hlim, hcover⟩ :=
      (F.metric t₀).exists_isometric_cone_limit_of_rescaled_normal_charts
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
      (fun k => Q (σ k)) (fun k => hQ (σ k)) (hQzero.comp hσ.tendsto_atTop)
      (fun k => q (σ k)) (fun k => Φ k) g hr (by linarith)
      hcenter' hradial'
      (by simpa only [ancientRescaleAt_metric, zero_div, add_zero] using hdist)
    refine ⟨τ, hτ, hL, hsource, U, hU, ψ, e, hrel, ?_, he, hlim, hcover⟩
    intro k x y hx hy z w hxz hyw
    exact hdistortion k ⟨x, hx⟩ ⟨y, hy⟩ z w hxz hyw

end PoincareConjecture.RicciFlow
