import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnularEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.LocalCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RadialIdentification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.SubsetChart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularDistance












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem ball_subset_image_closedBall_of_normal_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (q : M) {r S : ℝ} (hr : 0 < r) (hrS : r < S)
    (hsource : Φ.source = Metric.ball 0 S) (htarget : Φ.target = g.ball q S)
    (hradial : ∀ x ∈ Metric.ball 0 S, g.edist q (Φ x) = ENNReal.ofReal ‖x‖) :
    g.ball q r ⊆ Φ '' Metric.closedBall 0 r := by
  intro y hy
  have hyS : y ∈ Φ.target := by
    rw [htarget]
    exact lt_trans hy ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrS)).2 hrS)
  have hxS : Φ.symm y ∈ Metric.ball 0 S := hsource ▸ Φ.map_target hyS
  have heq : Φ (Φ.symm y) = y := Φ.right_inv hyS
  have hnorm : ‖Φ.symm y‖ < r := by
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
    rw [← hradial _ hxS, heq]
    exact hy
  exact ⟨Φ.symm y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm.le, heq⟩

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio




theorem cone_ball_subset_range_of_annulus_ball_coverage
    {X A : Type*} [MetricSpace X] [MetricSpace A] {p : X}
    (hcomparison : RayComparison p)
    (e : A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2) (o : A)
    {r : ℝ}
    (hradius : (asymptoticConeRadius hcomparison (e o) : ℝ) = 1)
    (hcover : Metric.ball (e o) r ⊆ range e) :
    Metric.ball (e o : AsymptoticCone p hcomparison) (min r (1 / 4)) ⊆
      range (fun x => (e x : AsymptoticCone p hcomparison)) := by
  intro z hz
  have hdist : dist z (e o : AsymptoticCone p hcomparison) < 1 / 4 :=
    hz.trans_le (min_le_right _ _)
  have hrad := (lipschitzWith_asymptoticConeRadius hcomparison).dist_le_mul z (e o)
  simp only [NNReal.coe_one, one_mul, NNReal.dist_eq, hradius] at hrad
  have hzann : z ∈ asymptoticConeClosedAnnulus hcomparison (1 / 2) 2 := by
    change 1 / 2 ≤ (asymptoticConeRadius hcomparison z : ℝ) ∧
      (asymptoticConeRadius hcomparison z : ℝ) ≤ 2
    have h := abs_le.mp hrad
    constructor <;> linarith
  have hzball : (⟨z, hzann⟩ : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2) ∈
      Metric.ball (e o) r := by
    change dist z (e o : AsymptoticCone p hcomparison) < r
    exact hz.trans_le (min_le_left _ _)
  obtain ⟨x, hx⟩ := hcover hzball
  exact ⟨x, congrArg Subtype.val hx⟩

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric





theorem cone_ball_subset_range_of_normal_chart_limit
    {n : ℕ} {M ι : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (gk : ι → RiemannianMetric n M)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M) (q : ι → M)
    (Φ : ι → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r S : ℝ} (hr : 0 < r) (hrS : r < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (gk k).ball (q k) S)
    (hcenter : ∀ k, Φ k 0 = q k)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (gk k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (L : ι → ℝ) (hL : ∀ k, 0 < L k)
    (hscale : ∀ k x y, ((gk k).edist x y).toReal = (g₀.edist x y).toReal / L k) :
    let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
    letI metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
    letI : PseudoEMetricSpace A := @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
    letI := g₀.toMetricSpace
    ∀ (hcomparison : RayComparison p)
      (ψ : ι → A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      (e : A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      {l : Filter ι} [l.NeBot] (ε τ : ι → ℝ),
      (∀ k, 0 < τ k) → Tendsto ε l (𝓝 0) →
      (∀ k (x : A), Φ k x ∈ rescaledClosedAnnulus p (L k) (1 / 2) 2) →
      (∀ k (x : A), annulusConeRelation hcomparison (L k) (τ k) (Φ k x) (ψ k x)) →
      (∀ k (x y : rescaledClosedAnnulus p (L k) (1 / 2) 2)
        (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
        annulusConeRelation hcomparison (L k) (τ k) x z →
        annulusConeRelation hcomparison (L k) (τ k) y w →
        |(g₀.edist (x : M) (y : M)).toReal / L k - dist z w| ≤ ε k) →
      Isometry e → TendstoUniformly ψ e l →
      Tendsto (fun k => ((gk k).edist p (q k)).toReal) l (𝓝 1) →
      Metric.ball (e ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison)
        (min r (1 / 4)) ⊆ range (fun x => (e x : AsymptoticCone p hcomparison)) := by
  classical
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  have hcompact : IsCompact A := isCompact_closedBall _ _
  let metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
  let : PseudoEMetricSpace A := @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
  let : CompactSpace A := isCompact_iff_compactSpace.mp hcompact
  let := g₀.toMetricSpace
  dsimp only
  intro hcomparison ψ e l hl ε τ hτ hε himage hrelated hdist he hlim hcenterlim
  let o : A := ⟨0, Metric.mem_closedBall_self hr.le⟩
  let X (k : ι) : Type _ := rescaledClosedAnnulus p (L k) (1 / 2) 2
  let sourceMetric (k : ι) : MetricSpace (X k) :=
    MetricSpace.induced Subtype.val Subtype.val_injective (gk k).toMetricSpace
  let φ : ∀ k, A → X k := fun k x => ⟨Φ k x, himage k x⟩
  let R : ∀ k, X k → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2 → Prop :=
    fun k x z => annulusConeRelation hcomparison (L k) (τ k) x z
  have hsourcecover : ∀ k (y : X k),
      ((gk k).edist (Φ k 0) (y : M)).toReal < r → ∃ x : A, φ k x = y := by
    intro k y hy
    have hyball : (y : M) ∈ (gk k).ball (q k) r := by
      let := (gk k).toMetricSpace
      rw [← (gk k).toMetricSpace_ball]
      change ((gk k).edist (y : M) (q k)).toReal < r
      rw [hcenter] at hy
      simpa only [← (gk k).toMetricSpace_dist, dist_comm] using hy
    obtain ⟨x, hx, hxy⟩ := (gk k).ball_subset_image_closedBall_of_normal_chart
      (Φ k) (q k) hr hrS (hsource k) (htarget k) (hradial k) hyball
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hcovered : Metric.ball (e o) r ⊆ range e := by
    have hecont : Continuous e := he.continuous
    apply ball_subset_range_of_uniform_relation_approximation X φ R ψ e o
      hecont hlim ε hε
    · exact Eventually.of_forall hrelated
    · apply Eventually.of_forall
      intro k x y z w hx hy
      change |((gk k).edist (x : M) (y : M)).toReal - dist z w| ≤ ε k
      rw [hscale]
      exact hdist k x y z w hx hy
    · exact Eventually.of_forall (fun k =>
        annulusConeRelation_surjective hcomparison (hL k) (hτ k))
    · exact Eventually.of_forall hsourcecover
  have hradiallim : Tendsto (fun k => dist p (Φ k 0) / L k) l
      (𝓝 (asymptoticConeRadius hcomparison (e o) : ℝ)) :=
    tendsto_normalized_radius_of_annulusConeRelation hcomparison
      (Eventually.of_forall hL) (Eventually.of_forall (fun k => hrelated k o))
      (continuous_subtype_val.tendsto _ |>.comp (hlim.tendsto_at o))
  have hradius : (asymptoticConeRadius hcomparison (e o) : ℝ) = 1 := by
    apply tendsto_nhds_unique hradiallim
    simpa only [g₀.toMetricSpace_dist, hcenter, ← hscale] using hcenterlim
  exact cone_ball_subset_range_of_annulus_ball_coverage hcomparison e o hradius hcovered




theorem exists_open_cone_chart_of_normal_chart_limit
    {n : ℕ} {M ι : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (gk : ι → RiemannianMetric n M)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (p : M) (q : ι → M)
    (Φ : ι → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r S : ℝ} (hr : 0 < r) (hrS : r < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (gk k).ball (q k) S)
    (hcenter : ∀ k, Φ k 0 = q k)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (gk k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (L : ι → ℝ) (hL : ∀ k, 0 < L k)
    (hscale : ∀ k x y, ((gk k).edist x y).toReal = (g₀.edist x y).toReal / L k) :
    let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
    letI metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
    letI : PseudoEMetricSpace A := @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
    letI := g₀.toMetricSpace
    ∀ (hcomparison : RayComparison p)
      (ψ : ι → A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      (e : A → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2)
      {l : Filter ι} [l.NeBot] (ε τ : ι → ℝ),
      (∀ k, 0 < τ k) → Tendsto ε l (𝓝 0) →
      (∀ k (x : A), Φ k x ∈ rescaledClosedAnnulus p (L k) (1 / 2) 2) →
      (∀ k (x : A), annulusConeRelation hcomparison (L k) (τ k) (Φ k x) (ψ k x)) →
      (∀ k (x y : rescaledClosedAnnulus p (L k) (1 / 2) 2)
        (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
        annulusConeRelation hcomparison (L k) (τ k) x z →
        annulusConeRelation hcomparison (L k) (τ k) y w →
        |(g₀.edist (x : M) (y : M)).toReal / L k - dist z w| ≤ ε k) →
      Isometry e → TendstoUniformly ψ e l →
      Tendsto (fun k => ((gk k).edist p (q k)).toReal) l (𝓝 1) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ min r (1 / 4) ∧
        ∃ (hδA : g.ball 0 δ ⊆ A)
          (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (AsymptoticCone p hcomparison)),
          F.source = g.ball 0 δ ∧
          F.target = Metric.ball
            (e ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison) δ ∧
          F 0 = (e ⟨0, Metric.mem_closedBall_self hr.le⟩ : AsymptoticCone p hcomparison) ∧
          (∀ x (hx : x ∈ g.ball 0 δ), F x = (e ⟨x, hδA hx⟩ : AsymptoticCone p hcomparison)) ∧
          (∀ x ∈ F.source, ∀ y ∈ F.source, dist (F x) (F y) = (g.edist x y).toReal) ∧
          (∀ x ∈ F.target, ∀ y ∈ F.target,
            (g.edist (F.symm x) (F.symm y)).toReal = dist x y) := by
  let A := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior A :=
    Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)
  let metricA : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective g.toMetricSpace
  let : PseudoEMetricSpace A := @PseudoMetricSpace.toPseudoEMetricSpace A metricA.toPseudoMetricSpace
  let := g₀.toMetricSpace
  dsimp only
  intro hcomparison ψ e l hl ε τ hτ hε himage hrelated hdist he hlim hcenterlim
  have hcoverage := g₀.cone_ball_subset_range_of_normal_chart_limit gk g p q Φ
    hr hrS hsource htarget hcenter hradial L hL hscale
    hcomparison ψ e ε τ hτ hε himage hrelated hdist he hlim hcenterlim
  let := g.toMetricSpace
  let e' : A → AsymptoticCone p hcomparison := fun x => e x
  have he' : Isometry e' := isometry_subtype_coe.comp he
  obtain ⟨δ, hδ, hδr, hδA, F, hFsource, hFtarget, hFcenter, hFe, hFdist, hFinv⟩ :=
    exists_openChart_of_isometry_subset_coverage hzero e' he'
      (lt_min hr (by norm_num)) hcoverage
  have hδA' : g.ball 0 δ ⊆ A := by simpa only [g.toMetricSpace_ball] using hδA
  refine ⟨δ, hδ, hδr, hδA', F, ?_, hFtarget, hFcenter, ?_, ?_, ?_⟩
  · simpa only [g.toMetricSpace_ball] using hFsource
  · intro x hx
    exact hFe x (by simpa only [g.toMetricSpace_ball] using hx)
  · simpa only [hFsource, g.toMetricSpace_dist] using hFdist
  · simpa only [hFtarget, g.toMetricSpace_dist] using hFinv

end PoincareConjecture.RiemannianMetric
