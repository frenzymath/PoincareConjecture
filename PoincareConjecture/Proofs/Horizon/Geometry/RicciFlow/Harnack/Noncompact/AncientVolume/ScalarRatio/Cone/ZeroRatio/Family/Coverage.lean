import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ChartCoverage











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem cone_ball_subset_range_of_metricCoordinateBall_normal_chart_limit
    {n : ℕ} {M ι : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (gk : ι → RiemannianMetric n M)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M) (q : ι → M)
    (Φ : ι → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r S : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8) (hrS : r < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (gk k).ball (q k) S)
    (hcenter : ∀ k, Φ k 0 = q k)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (gk k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (L : ι → ℝ) (hL : ∀ k, 0 < L k)
    (hscale : ∀ k x y, ((gk k).edist x y).toReal = (g₀.edist x y).toReal / L k) :
    letI := g₀.toMetricSpace
    ∀ (hcomparison : RayComparison p)
      (ψ : ι → MetricCoordinateBall g r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      (e : MetricCoordinateBall g r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      {l : Filter ι} [l.NeBot] (ε τ : ι → ℝ),
      (∀ k, 0 < τ k) → Tendsto ε l (𝓝 0) →
      (∀ k (x : MetricCoordinateBall g r),
        Φ k x.val ∈ rescaledClosedAnnulus p (L k) (1 / 2) 2) →
      (∀ k (x : MetricCoordinateBall g r),
        annulusConeRelation hcomparison (L k) (τ k) (Φ k x.val) (ψ k x)) →
      (∀ k (x y : rescaledClosedAnnulus p (L k) (1 / 2) 2)
        (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
        annulusConeRelation hcomparison (L k) (τ k) x z →
        annulusConeRelation hcomparison (L k) (τ k) y w →
        |(g₀.edist (x : M) (y : M)).toReal / L k - dist z w| ≤ ε k) →
      Isometry e → TendstoUniformly ψ e l →
      Tendsto (fun k => ((gk k).edist p (q k)).toReal) l (𝓝 1) →
      Metric.ball (e ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison) r ⊆
        range (fun x => (e x : AsymptoticCone p hcomparison)) := by
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let metricA : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
  let : PseudoEMetricSpace A :=
    @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
  let := g₀.toMetricSpace
  intro hcomparison ψ e l hl ε τ hτ hε himage hrelated hdist he hlim hcenterlim
  let c : A → MetricCoordinateBall g r := fun x => ⟨x.val, x.property⟩
  have hc : Isometry c := fun _ _ => rfl
  have hcoverage := g₀.cone_ball_subset_range_of_normal_chart_limit gk g p q Φ
    hr hrS hsource htarget hcenter hradial L hL hscale hcomparison
    (fun k x => ψ k (c x)) (fun x => e (c x)) ε τ hτ hε
    (fun k x => himage k (c x)) (fun k x => hrelated k (c x)) hdist
    (he.comp hc) (hlim.comp c) hcenterlim
  rw [min_eq_left (show r ≤ 1 / 4 by linarith)] at hcoverage
  intro z hz
  obtain ⟨x, hx⟩ := hcoverage hz
  exact ⟨c x, hx⟩



theorem metricCoordinateBall_cone_limit_center_eq_ray
    {n : ℕ} {M ι : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M)
    {r : ℝ} (hr : 0 < r) :
    letI := g₀.toMetricSpace
    ∀ (hcomparison : RayComparison p) (η : basedMinimizingRays p)
      (Φ : ι → EuclideanSpace ℝ (Fin n) → M)
      (ψ : ι → MetricCoordinateBall g r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      (e : MetricCoordinateBall g r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      {l : Filter ι} [l.NeBot] (L τ : ι → ℝ),
      (∀ k, 0 < L k) → Tendsto τ l (𝓝 0) →
      (∀ k, Φ k 0 = rayExtension η (L k)) →
      (∀ k x, annulusConeRelation hcomparison (L k) (τ k) (Φ k x.val) (ψ k x)) →
      TendstoUniformly ψ e l →
      (e ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison) =
        asymptoticConeRayProjection hcomparison (1, η) := by
  let := g₀.toMetricSpace
  intro hcomparison η Φ ψ e l hl L τ hL hτ hcenter hrel hlim
  let o : MetricCoordinateBall g r := ⟨0, Metric.mem_closedBall_self hr.le⟩
  have hactual := tendsto_unit_cone_of_annulusConeRelation_ray hcomparison η
    (Eventually.of_forall hL) hτ (Eventually.of_forall (fun k => by
      simpa only [o, hcenter] using hrel k o))
  exact tendsto_nhds_unique
    (continuous_subtype_val.tendsto _ |>.comp (hlim.tendsto_at o)) hactual




theorem cone_balls_subset_ranges_of_normal_chart_family_on_rays
    {n : ℕ} {M ι : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (gk : ι → RiemannianMetric n M)
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M)
    {r S : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8) (hrS : r < S)
    (L : ι → ℝ) (hL : ∀ k, 0 < L k)
    (hscale : ∀ k x y, ((gk k).edist x y).toReal = (g₀.edist x y).toReal / L k) :
    letI := g₀.toMetricSpace
    ∀ (hcomparison : RayComparison p) (η : ℕ → basedMinimizingRays p)
      (Φ : ι → ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
      (ψ : ι → ∀ j, MetricCoordinateBall (g j) r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      (e : ∀ j, MetricCoordinateBall (g j) r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      {l : Filter ι} [l.NeBot] (ε τ : ι → ℝ),
      (∀ k j, (Φ k j).source = Metric.ball 0 S) →
      (∀ k j, (Φ k j).target = (gk k).ball (rayExtension (η j) (L k)) S) →
      (∀ k j, Φ k j 0 = rayExtension (η j) (L k)) →
      (∀ k j x, x ∈ Metric.ball 0 S →
        (gk k).edist (rayExtension (η j) (L k)) (Φ k j x) = ENNReal.ofReal ‖x‖) →
      (∀ k, 0 < τ k) → Tendsto ε l (𝓝 0) → Tendsto τ l (𝓝 0) →
      (∀ k j (x : MetricCoordinateBall (g j) r),
        Φ k j x.val ∈ rescaledClosedAnnulus p (L k) (1 / 2) 2) →
      (∀ k j (x : MetricCoordinateBall (g j) r),
        annulusConeRelation hcomparison (L k) (τ k) (Φ k j x.val) (ψ k j x)) →
      (∀ k (x y : rescaledClosedAnnulus p (L k) (1 / 2) 2)
        (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
        annulusConeRelation hcomparison (L k) (τ k) x z →
        annulusConeRelation hcomparison (L k) (τ k) y w →
        |(g₀.edist (x : M) (y : M)).toReal / L k - dist z w| ≤ ε k) →
      (∀ j, Isometry (e j)) → (∀ j, TendstoUniformly (fun k => ψ k j) (e j) l) →
      ∀ j,
        (e j ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison) =
          asymptoticConeRayProjection hcomparison (1, η j) ∧
        Metric.ball (asymptoticConeRayProjection hcomparison (1, η j)) r ⊆
          range (fun x => (e j x : AsymptoticCone p hcomparison)) := by
  let := g₀.toMetricSpace
  intro hcomparison η Φ ψ e l hl ε τ hsource htarget hcenter hradial
    hτ hε hτlim himage hrel hdist he hlim j
  have hcenterlim : Tendsto
      (fun k => ((gk k).edist p (rayExtension (η j) (L k))).toReal) l (𝓝 1) := by
    have hconstant : (fun k => ((gk k).edist p (rayExtension (η j) (L k))).toReal) =
        fun _ => (1 : ℝ) := by
      funext k
      rw [hscale]
      have hdistRay : (g₀.edist p (rayExtension (η j) (L k))).toReal = L k := by
        change dist p (rayExtension (η j) (L k)) = L k
        simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_pos (hL k)] using
          rayExtension_dist (η j) (le_refl 0) (hL k).le
      rw [hdistRay, div_self (hL k).ne']
    rw [hconstant]
    exact tendsto_const_nhds
  have hcenterEq := g₀.metricCoordinateBall_cone_limit_center_eq_ray (g j) p hr
    hcomparison (η j) (fun k => Φ k j) (fun k => ψ k j) (e j) L τ hL hτlim
    (fun k => hcenter k j) (fun k x => hrel k j x) (hlim j)
  refine ⟨hcenterEq, ?_⟩
  rw [← hcenterEq]
  exact g₀.cone_ball_subset_range_of_metricCoordinateBall_normal_chart_limit gk (g j) p
    (fun k => rayExtension (η j) (L k)) (fun k => Φ k j) hr hrsmall hrS
    (fun k => hsource k j) (fun k => htarget k j) (fun k => hcenter k j)
    (fun k => hradial k j) L hL hscale hcomparison (fun k => ψ k j) (e j)
    ε τ hτ hε (fun k => himage k j) (fun k => hrel k j) hdist (he j) (hlim j) hcenterlim

end PoincareConjecture.RiemannianMetric
