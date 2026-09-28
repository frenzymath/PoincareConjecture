import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.RadialRealization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.Coverage








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem exists_radial_cone_realization_of_normal_chart_family_on_rays
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (D₀ : LeviCivitaData g₀)
    (hcomplete : MetricComplete g₀) (hsec : D₀.NonnegativeSectionalCurvature) (p : M)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (hQzero : Tendsto Q atTop (𝓝 0))
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r S : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8) (hrS : r < S) :
    letI := g₀.toMetricSpace
    let hc := g₀.rayComparison_of_metricComplete D₀ hcomplete hsec p
    let L := fun k => 1 / Real.sqrt (Q k)
    ∀ (η : ℕ → basedMinimizingRays p)
      (Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
      (δ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = (rescaledMetric g₀ (Q k) (hQ k)).ball (rayExtension (η j) (L k)) S ∧
        Φ k j 0 = rayExtension (η j) (L k) ∧
        ∀ x ∈ Metric.ball 0 S,
          (rescaledMetric g₀ (Q k) (hQ k)).edist (rayExtension (η j) (L k)) (Φ k j x) =
            ENNReal.ofReal ‖x‖) →
      (∀ j, TendstoUniformlyOn
        (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k j z.1) (Φ k j z.2)).toReal)
        (fun z => ((g j).edist z.1 z.2).toReal) atTop
        (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r)) →
      (∀ i j x, x ∈ Metric.closedBall 0 r → ∀ y, y ∈ Metric.closedBall 0 r →
        Tendsto (fun k => ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k i x) (Φ k j y)).toReal)
          atTop (𝓝 (δ i j x y))) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc,
        (∀ j, Isometry (e j)) ∧
        (∀ i j x y, dist (e i x) (e j y) = δ i j x.val y.val) ∧
        (∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η j)) ∧
        (∀ j, Metric.ball (asymptoticConeRayProjection hc (1, η j)) r ⊆ range (e j)) ∧
        ∀ j, TendstoUniformly
          (fun k (x : MetricCoordinateBall (g j) r) =>
            ((rescaledMetric g₀ (Q (σ k)) (hQ (σ k))).edist p (Φ (σ k) j x.val)).toReal)
          (fun x => (asymptoticConeRadius hc (e j x) : ℝ)) atTop := by
  let := g₀.toMetricSpace
  let hc := g₀.rayComparison_of_metricComplete D₀ hcomplete hsec p
  let L := fun k => 1 / Real.sqrt (Q k)
  dsimp only
  intro η Φ δ hcharts hdist hcross
  have hL (k : ℕ) : 0 < L k := one_div_pos.mpr (Real.sqrt_pos.mpr (hQ k))
  have hscale (k : ℕ) (x y : M) :
      ((rescaledMetric g₀ (Q k) (hQ k)).edist x y).toReal = (g₀.edist x y).toReal / L k := by
    rw [rescaledMetric_edist, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    dsimp only [L]
    rw [div_div_eq_mul_div, div_one, mul_comm]
  have hcenter (k j : ℕ) :
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (rayExtension (η j) (L k))).toReal = 1 := by
    rw [hscale]
    have hrad : (g₀.edist p (rayExtension (η j) (L k))).toReal = L k := by
      change dist p (rayExtension (η j) (L k)) = L k
      simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_pos (hL k)] using
        rayExtension_dist (η j) (le_refl 0) (hL k).le
    rw [hrad, div_self (hL k).ne']
  obtain ⟨τ, hτ, hLτ, himage, U, hU, ψ, e, hrel, hdistortion, he, hlim, hδ, _⟩ :=
    g₀.exists_common_cone_limit_of_rescaled_normal_chart_family D₀ hcomplete hsec p Q hQ hQzero
      (fun j k => rayExtension (η j) (L k)) (fun k j => Φ k j) g hr hrsmall
      (fun k j => by rw [hcenter]; norm_num)
      (fun k j x hx => (hcharts k j).2.2.2 x
        (Metric.closedBall_subset_ball hrS hx)) hdist δ hcross
  have hε : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) (U : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hU
  have hτzero : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) / 4) (U : Filter ℕ) (𝓝 0) := by
    simpa only [zero_div] using hε.div_const 4
  have hcoverage := g₀.cone_balls_subset_ranges_of_normal_chart_family_on_rays
    (fun k => rescaledMetric g₀ (Q (τ k)) (hQ (τ k))) g p hr hrsmall hrS
    (fun k => L (τ k)) hLτ (fun k => hscale (τ k)) hc η (fun k => Φ (τ k)) ψ e
    (fun k : ℕ => 1 / ((k : ℝ) + 1)) (fun k : ℕ => (1 / ((k : ℝ) + 1)) / 4)
    (fun k j => (hcharts (τ k) j).1) (fun k j => (hcharts (τ k) j).2.1)
    (fun k j => (hcharts (τ k) j).2.2.1) (fun k j => (hcharts (τ k) j).2.2.2)
    (fun k => by positivity) hε hτzero himage hrel
    (fun k x y z w hx hy => (hdistortion k x y z w hx hy).le) he hlim
  obtain ⟨σ, hσ, hradial⟩ :=
    exists_strictMono_normalized_radius_limits_of_annulusConeRelation hc hU τ hτ L hLτ
      (fun k j (x : MetricCoordinateBall (g j) r) => Φ k j x.val)
      (fun k j x => (ψ k j x).val) (fun j x => (e j x).val)
      (fun k : ℕ => (1 / ((k : ℝ) + 1)) / 4) hrel
      (fun j => isometry_subtype_coe.uniformContinuous.comp_tendstoUniformly (hlim j))
  refine ⟨σ, hσ, fun j x => (e j x).val,
    fun j => isometry_subtype_coe.comp (he j), hδ,
    (fun j => (hcoverage j).1), (fun j => (hcoverage j).2), fun j => ?_⟩
  simpa only [hscale, toMetricSpace_dist] using hradial j



theorem exists_cone_realization_of_normal_chart_family_on_rays
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (D₀ : LeviCivitaData g₀)
    (hcomplete : MetricComplete g₀) (hsec : D₀.NonnegativeSectionalCurvature) (p : M)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (hQzero : Tendsto Q atTop (𝓝 0))
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r S : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8) (hrS : r < S) :
    letI := g₀.toMetricSpace
    let hc := g₀.rayComparison_of_metricComplete D₀ hcomplete hsec p
    let L := fun k => 1 / Real.sqrt (Q k)
    ∀ (η : ℕ → basedMinimizingRays p)
      (Φ : ℕ → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
      (δ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ k j, (Φ k j).source = Metric.ball 0 S ∧
        (Φ k j).target = (rescaledMetric g₀ (Q k) (hQ k)).ball (rayExtension (η j) (L k)) S ∧
        Φ k j 0 = rayExtension (η j) (L k) ∧
        ∀ x ∈ Metric.ball 0 S,
          (rescaledMetric g₀ (Q k) (hQ k)).edist (rayExtension (η j) (L k)) (Φ k j x) =
            ENNReal.ofReal ‖x‖) →
      (∀ j, TendstoUniformlyOn
        (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k j z.1) (Φ k j z.2)).toReal)
        (fun z => ((g j).edist z.1 z.2).toReal) atTop
        (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r)) →
      (∀ i j x, x ∈ Metric.closedBall 0 r → ∀ y, y ∈ Metric.closedBall 0 r →
        Tendsto (fun k => ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k i x) (Φ k j y)).toReal)
          atTop (𝓝 (δ i j x y))) →
      ∃ e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc,
        (∀ j, Isometry (e j)) ∧
        (∀ i j x y, dist (e i x) (e j y) = δ i j x.val y.val) ∧
        (∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η j)) ∧
        ∀ j, Metric.ball (asymptoticConeRayProjection hc (1, η j)) r ⊆ range (e j) := by
  let := g₀.toMetricSpace
  dsimp only
  intro η Φ δ hcharts hdist hcross
  obtain ⟨σ, hσ, e, he, hδ, hcenter, hcover, hradial⟩ :=
    g₀.exists_radial_cone_realization_of_normal_chart_family_on_rays
      D₀ hcomplete hsec p Q hQ hQzero g hr hrsmall hrS η Φ δ hcharts hdist hcross
  exact ⟨e, he, hδ, hcenter, hcover⟩

end PoincareConjecture.RiemannianMetric
