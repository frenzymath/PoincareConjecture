import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Transitions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Finite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

theorem normal_chart_restriction_geometry
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T3Space (M k)]
    [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (q : ∀ k, ℕ → M k)
    (Φ : ∀ k, ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    {S r : ℝ} (hr : 0 < r) (hrS : 3 * r ≤ S)
    (hsource : ∀ k j, (Φ k j).source = Metric.ball 0 S)
    (htarget : ∀ k j, (Φ k j).target = (g k).ball (q k j) S)
    (hradial : ∀ k j x, x ∈ Metric.ball 0 S →
      (g k).edist (q k j) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (helliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients (Φ k j) x v v ∧
      (g k).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) :
    letI : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
    let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
    letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    let e : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
    (∀ k i, LipschitzWith (3 / 2 : ℝ≥0) (e k i)) ∧
      (∀ k i x y, (1 / 2 : ℝ) * dist x y ≤ dist (e k i x) (e k i y)) ∧
      (∀ k i, Topology.IsOpenEmbedding (e k i)) ∧
      (∀ k (p : M k) s, IsPreconnected (Metric.ball p s)) ∧
      (letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => letI : Nonempty (U i) := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
          (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
        ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i)) := by
  let : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  let e : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
  have hs (k i : ℕ) : U i ⊆ (Φ k i).source := by
    rw [hsource]
    exact Metric.ball_subset_ball (by linarith)
  have hdist (k i : ℕ) (x y : Piece U i) :
      (1 / 2 : ℝ) * dist x y ≤ dist (e k i x) (e k i y) ∧
        dist (e k i x) (e k i y) ≤ (3 / 2 : ℝ) * dist x y := by
    have hh := (g k).toReal_edist_bounds_of_normal_pullback_bounds (q k i) (Φ k i)
      hr hrS (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) ≤ 9 / 4)
      (hsource k i) (htarget k i) (hradial k i) (helliptic k i) x.property y.property
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [Real.sqrt_div, h4, h9] at hh
    exact hh
  refine ⟨?_, fun k i x y => (hdist k i x y).1, ?_, ?_, ?_⟩
  · intro k i
    exact LipschitzWith.of_dist_le_mul (fun x y => by simpa using (hdist k i x y).2)
  · intro k i
    exact (Φ k i).toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp
      (Topology.IsOpenEmbedding.inclusion (hs k i) ((hU i).preimage continuous_subtype_val))
  · intro k p s
    rw [(g k).toMetricSpace_ball]
    exact (g k).isPreconnected_ball p s
  · intro k i
    let : Nonempty (U i) := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    exact isLocalDiffeomorph_normal_chart_restrict (Φ k i) (U i) (hU i) (hs k i)

theorem exists_local_source_models_of_normal_chart_limits
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T3Space (M k)]
    [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (q : ∀ k, ℕ → M k)
    (Φ : ∀ k, ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    (h : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {S r : ℝ} (hr : 0 < r) (hrS : 3 * r ≤ S)
    (hsource : ∀ k j, (Φ k j).source = Metric.ball 0 S)
    (htarget : ∀ k j, (Φ k j).target = (g k).ball (q k j) S)
    (hradial : ∀ k j x, x ∈ Metric.ball 0 S →
      (g k).edist (q k j) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (helliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients (Φ k j) x v v ∧
      (g k).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hjets : ∀ j m C, IsCompact C → C ⊆ Metric.ball 0 r → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (Φ k j)))
      (iteratedFDeriv ℝ m (h j).euclideanCoefficients) atTop C) :
    letI : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
    let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
    letI : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    let e : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
    let hgeom := normal_chart_restriction_geometry g q Φ hr hrS hsource htarget hradial helliptic
    ∀ (d : ∀ i j, C(Piece U i × Piece U j, ℝ))
      (hd : ∀ i j, TendstoLocallyUniformly
        (fun k (z : Piece U i × Piece U j) => dist (e k i z.1) (e k j z.2)) (d i j) atTop),
    letI : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
    let O := ChartDistance.overlapSystem
      (fun i j x y => (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
      (fun _ => 3 / 2) hgeom.1 (fun _ => 1 / 2) (fun _ => by norm_num)
      hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
    letI := quotientChartedSpace U hU O
    ∀ (i₀ : ℕ) (C₀ : Set (Piece U i₀)), IsCompact C₀ →
      ∀ K : Set (Quotient O.setoid), IsCompact K →
        ∃ V : Set (Quotient O.setoid), IsOpen V ∧ IsCompact (closure V) ∧
          K ∪ O.include i₀ '' C₀ ⊆ V ∧
        ∃ F : ∀ k, Quotient O.setoid → M k,
          ChartDistance.HasLocalSourceModels U hU O e F V ∧
          ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x) ∧
            IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) V ∧
            ∀ y ∈ C₀, F k (O.include i₀ y) = e k i₀ y := by
  let : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
  let U := fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  let e : ∀ k i, Piece U i → M k := fun k i x => Φ k i x
  have hgeom := normal_chart_restriction_geometry g q Φ hr hrS hsource htarget hradial helliptic
  dsimp only
  intro d hd
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let hp := fun i j x y => (hd i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := ChartDistance.overlapSystem hp (fun _ => 3 / 2) hgeom.1
    (fun _ => 1 / 2) (fun _ => by norm_num) hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1
  let := quotientChartedSpace U hU O
  intro i₀ C₀ hC₀ K hK
  have htrans := locallyEventuallyBoundedDerivatives_normal_chart_transition g q Φ h
    hr hrS hsource htarget hradial helliptic hjets d hp
  exact ChartDistance.exists_local_source_models_near_compact U hU hd
    (fun _ => 3 / 2) hgeom.1 (fun _ => 1 / 2) (fun _ => by norm_num)
    hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2 htrans i₀ hC₀ K hK

end PoincareConjecture.RiemannianMetric
