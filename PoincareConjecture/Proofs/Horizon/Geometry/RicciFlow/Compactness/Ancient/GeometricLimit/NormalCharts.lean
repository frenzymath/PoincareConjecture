import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Rescaling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
noncomputable section

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

local instance ancientNormal_sourceTopology (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance ancientNormal_sourceCharts (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance ancientNormal_sourceManifold (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold
local instance ancientNormal_sourceMetric (k : ℕ) : MetricSpace (S.carrier k).carrier :=
  (S.carrier k).metricSpaceOf ((S.flow k).metricAt 0)



theorem exists_complete_ancient_geometric_limit
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (S.carrier k).carrier (J k))
    (hmetric : ∀ k, (Fseq k).metric = (S.flow k).flow.metric)
    {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ s t : ℝ, t < δ → ∀ᶠ k in atTop, Icc s t ⊆ J k)
    {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover (S.flow k).flow.metric
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (ha : ∀ j, 0 < a j)
    (hraw : ∀ i : ℕ,
      let raw := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      LocallyEventuallyContDiff (Iio δ ×ˢ ball 0 (ρ (Nat.unpair i).1)) raw ∧
      (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
        K ⊆ Iio δ ×ˢ ball 0 (ρ (Nat.unpair i).1) → ∀ d : ℕ, ∃ B : ℝ,
          ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
      (∀ t ∈ Iio δ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        ∀ x ∈ ball 0 (ρ (Nat.unpair i).1), ∀ v,
          c * ‖v‖ ^ 2 ≤ raw k (t, x) v v)) :
    ∃ G : AncientPointedGeometricConvergence S.carrier (fun k => (Fseq k).metric)
        (fun k => (S.flow k).base) δ,
      letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      G.limitCarrier.metricComplete (G.limitFlow.metric 0) := by
  classical
  let U := fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1
  have hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, by simp [U]⟩⟩
  let e := diagonalUnitBallMap cover
  choose L c hc hL hlower using diagonalUnitBallMap_distance_bounds cover hρ ha
  have hpositive (i : ℕ) (t : ℝ) (ht : t ∈ Iio δ) :=
    diagonalUnitBallMap_eventually_lower_coefficients_of_raw cover hρ hρR i t
      ((hraw i).2.2 t ht)
  apply ChartDistance.exists_complete_ancient_geometric_limit_of_controlled_charts
    S.carrier Fseq (fun k => (S.flow k).base) hδ htime U hU e L
    (by
      intro k i
      have hdist := (hL i k).dist_le_mul
      let : MetricSpace (S.carrier k).carrier :=
        (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using
        hdist x y) c hc
    (by
      intro k i x y
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using
        hlower i k x y)
    (diagonalUnitBallMap_isOpenEmbedding cover hρ hρR)
    (diagonalUnitBallMap_isLocalDiffeomorph cover hρ hρR)
    (by
      intro i j x y
      obtain ⟨B, hB⟩ := diagonalUnitBallMap_pairwise_bounded cover L
        (fun k i => hL i k) i j x y
      refine ⟨B, fun k => ?_⟩
      simpa only [FlowCarrier.dist_metricSpaceOf, hmetric, BasedFlow.metricAt, e] using hB k)
    (i₀ := 0) ⟨0, by simp [U]⟩ (diagonalUnitBallMap_zero cover)
  · intro R hR
    obtain ⟨s, K, hK, hcov⟩ := diagonalUnitBallMap_compact_cover cover hρ R hR
    refine ⟨s, K, hK, ?_⟩
    filter_upwards [hcov] with k hk
    simpa only [FlowCarrier.metricBall_eq_metricBallOf, hmetric, BasedFlow.metricAt,
      e, diagonalUnitBallMap_zero] using hk
  · intro i K _ hKU
    obtain ⟨d, hd, hbound⟩ := hpositive i 0 hδ
    refine ⟨d, hd, ?_⟩
    simpa only [hmetric] using hbound.mono
      (fun k hk x hx v => hk x (hKU hx) v)
  · intro i
    simpa only [hmetric] using
      diagonalUnitBallMap_eventually_bounded_spacetime_derivatives_on_open
        cover hρ hρR i isOpen_Iio (hraw i).1 (hraw i).2.1
  · intro t ht i x hx
    obtain ⟨d, hd, hbound⟩ := hpositive i t ht
    refine ⟨d, hd, ?_⟩
    simpa only [hmetric] using hbound.mono (fun k hk v => hk x hx v)

end PoincareConjecture.NormalChartCover
