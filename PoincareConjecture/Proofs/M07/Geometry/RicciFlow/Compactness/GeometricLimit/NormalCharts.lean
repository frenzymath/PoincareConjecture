import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.CoordinateLimit
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Rescaling
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.ZeroDimension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

local instance (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance (k : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold
local instance (k : ℕ) : MetricSpace (S.carrier k).carrier :=
  (S.carrier k).metricSpaceOf ((S.flow k).metricAt 0)

theorem exists_complete_geometric_limit
    (hT : T' < 0 ∧ 0 < T) {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (ha : ∀ j, 0 < a j)
    (hjets : ∀ i (K : Set (ℝ × EuclideanSpace ℝ (Fin n))), IsCompact K →
      K ⊆ Ioo T' T ×ˢ ball 0 (ρ (Nat.unpair i).1) → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow k).flow.metric z.1).pullbackCoefficients
            ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
              ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
                Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2) z‖ ≤ B) :
    ∃ G : PointedGeometricConvergence S,
      G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) := by
  classical
  let U := fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1
  have hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : ∀ i, Nonempty (Piece U i) := fun _ => ⟨⟨0, by simp [U]⟩⟩
  let e := diagonalUnitBallMap cover
  choose L c hc hL hlower using diagonalUnitBallMap_distance_bounds cover hρ ha
  have hpositive := diagonalUnitBallMap_eventually_lower_coefficients cover hρ hρR ha
  apply ChartDistance.exists_complete_geometric_limit_of_controlled_charts
    S hT U hU e L (fun k i => hL i k) c hc (fun k i => hlower i k)
    (diagonalUnitBallMap_isOpenEmbedding cover hρ hρR)
    (diagonalUnitBallMap_isLocalDiffeomorph cover hρ hρR)
    (diagonalUnitBallMap_pairwise_bounded cover L (fun k i => hL i k))
    (i₀ := 0) ⟨0, by simp [U]⟩ (diagonalUnitBallMap_zero cover)
  · simpa only [e, diagonalUnitBallMap_zero] using diagonalUnitBallMap_compact_cover cover hρ
  · intro i K _ hKU
    obtain ⟨d, hd, hbound⟩ := hpositive i
    exact ⟨d, hd, hbound.mono fun k hk x hx v => hk 0 hT x (hKU hx) v⟩
  · exact fun i => diagonalUnitBallMap_eventually_bounded_spacetime_derivatives
      cover hρ hρR i (hjets i)
  · intro t ht i x hx
    obtain ⟨d, hd, hbound⟩ := hpositive i
    exact ⟨d, hd, hbound.mono fun k hk v => hk t ht x hx v⟩

end PoincareConjecture.NormalChartCover

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

theorem pointedRicciFlowCompactness_of_uniform_normalChartCover_bounds
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hjets : ∀ (A R ρ a b : ℝ) (N : ℕ), 0 < A → 0 < ρ → 2 * ρ < R →
      0 < a → 0 < b → ∀ I : Set ℝ, IsCompact I → I ⊆ Ioo T' T → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop,
        let C := H.sequence.carrier k
        let F := H.sequence.flow k
        letI : TopologicalSpace C.carrier := C.topologicalSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
        letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
        ∀ cover : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
          ∀ l t, t ∈ I → ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ,
            ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              (F.metricAt z.1).pullbackCoefficients (cover.chart l) z.2) (t, x)‖ ≤ B) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact pointedRicciFlowCompactness_zero H
  have hn' : 1 ≤ n := by omega
  obtain ⟨σ, hσ, R, ρ, a, b, N, hconstants, hcovers⟩ :=
    H.exists_diagonal_normalChartCovers hn'
  let S := H.sequence.subsequence σ
  let : ∀ k, TopologicalSpace (S.carrier k).carrier := fun k => (S.carrier k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
    fun k => (S.carrier k).chartedSpace
  let : ∀ k, IsManifold (𝓡 n) ∞ (S.carrier k).carrier := fun k => (S.carrier k).isManifold
  let cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => (hcovers k j hjk).choose
  have hρ : ∀ j, 0 < ρ j := fun j => (hconstants j).1
  have hρR : ∀ j, ρ j / 2 ≤ R j := by
    intro j
    have := (hconstants j).2.1
    have := hρ j
    linarith
  have ha : ∀ j, 0 < a j := fun j => (hconstants j).2.2.1
  obtain ⟨G, hcomplete⟩ := NormalChartCover.exists_complete_geometric_limit
    H.time_bounds cover hρ hρR ha (by
      intro i K hK hKU m
      let j := (Nat.unpair i).1
      have hI : IsCompact (Prod.fst '' K) := hK.image continuous_fst
      have hIT : Prod.fst '' K ⊆ Ioo T' T := by
        rintro t ⟨z, hz, rfl⟩
        exact (hKU hz).1
      obtain ⟨B, hB⟩ := hjets ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j)
        (by positivity) (hρ j) (hconstants j).2.1 (ha j) (hconstants j).2.2.2
        (Prod.fst '' K) hI hIT m
      refine ⟨B, ?_⟩
      filter_upwards [hσ.tendsto_atTop.eventually hB, eventually_ge_atTop j] with k hk hjk z hz
      have hbound := hk (cover k j hjk)
        ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ z.1
        (mem_image_of_mem Prod.fst hz) z.2
        (ball_subset_closedBall (hKU hz).2)
      let field := fun q (hq : q ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k q hq).chart
            ⟨(Nat.unpair i).2 % (N q + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      change ‖iteratedFDeriv ℝ m
        (field (min (Nat.unpair i).1 k) (min_le_right _ _)) z‖ ≤ B
      have hmin : min (Nat.unpair i).1 k = j := min_eq_left hjk
      have heq : field (min (Nat.unpair i).1 k) (min_le_right _ _) = field j hjk := by
        congr 1
        exact min_le_right _ _
      rw [heq]
      exact hbound)
  exact pointedRicciFlowCompactness_of_geometric_limit (G.ofSubsequence hσ) hcomplete

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
