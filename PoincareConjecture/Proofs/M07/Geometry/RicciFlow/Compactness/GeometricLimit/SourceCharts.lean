import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.IndexedDistanceBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.DiagonalCovering
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric
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

variable {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))

private def stageUnitBallMap (k j : ℕ) (hjk : j ≤ k) (l : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : (S.carrier k).carrier :=
  (cover k j hjk).unitBallMap ⟨l % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ x

def diagonalUnitBallMap (k i : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : (S.carrier k).carrier :=
  stageUnitBallMap cover k (min (Nat.unpair i).1 k) (min_le_right _ _)
    (Nat.unpair i).2 x

theorem diagonalUnitBallMap_of_le (k i : ℕ) (hik : (Nat.unpair i).1 ≤ k) :
    diagonalUnitBallMap cover k i =
      (cover k (Nat.unpair i).1 hik).unitBallMap
        ⟨(Nat.unpair i).2 % (N (Nat.unpair i).1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  funext x
  simp only [diagonalUnitBallMap, min_eq_left hik]
  rfl

theorem diagonalUnitBallMap_pair (k j : ℕ) (hjk : j ≤ k) (l : Fin (N j + 1)) :
    diagonalUnitBallMap cover k (Nat.pair j l) = (cover k j hjk).unitBallMap l := by
  funext x
  simp only [diagonalUnitBallMap, Nat.unpair_pair, min_eq_left hjk]
  simp only [stageUnitBallMap, Nat.mod_eq_of_lt l.isLt]

theorem diagonalUnitBallMap_zero (k : ℕ) :
    diagonalUnitBallMap cover k 0 ⟨0, by simp⟩ = (S.flow k).base := by
  change diagonalUnitBallMap cover k (Nat.pair 0 (0 : Fin (N 0 + 1))) ⟨0, by simp⟩ = _
  rw [diagonalUnitBallMap_pair cover k 0 (Nat.zero_le k) (0 : Fin (N 0 + 1))]
  simp only [unitBallMap, smul_zero]
  exact ((cover k 0 (Nat.zero_le k)).map_zero 0).trans
    (cover k 0 (Nat.zero_le k)).centre_zero

theorem diagonalUnitBallMap_isLocalDiffeomorph
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    letI : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
    letI := (isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (diagonalUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isLocalDiffeomorph (hρ _) (hρR _) _

theorem diagonalUnitBallMap_isOpenEmbedding
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    Topology.IsOpenEmbedding (diagonalUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isOpenEmbedding (hρ _) (hρR _) _

theorem diagonalUnitBallMap_distance_bounds
    (hρ : ∀ j, 0 < ρ j) (ha : ∀ j, 0 < a j) (i : ℕ) :
    ∃ L : ℝ≥0, ∃ c : ℝ, 0 < c ∧
      (∀ k, LipschitzWith L (diagonalUnitBallMap cover k i)) ∧
      ∀ k x y, c * dist x y ≤
        dist (diagonalUnitBallMap cover k i x) (diagonalUnitBallMap cover k i y) := by
  classical
  let s := Finset.range ((Nat.unpair i).1 + 1)
  have hs : s.Nonempty := ⟨0, by simp [s]⟩
  let upper := fun j => Real.sqrt (b j) * (ρ j / 2)
  let lower := fun j => Real.sqrt (a j) * (ρ j / 2)
  have hupper (j : ℕ) : 0 ≤ upper j := mul_nonneg (Real.sqrt_nonneg _) (half_pos (hρ j)).le
  have hlower (j : ℕ) : 0 < lower j := mul_pos (Real.sqrt_pos.2 (ha j)) (half_pos (hρ j))
  let B := s.sup' hs upper
  have hB : 0 ≤ B := (hupper 0).trans (Finset.le_sup' upper (by simp [s]))
  let c := s.inf' hs lower
  have hc : 0 < c := (Finset.lt_inf'_iff hs).2 (fun j _ => hlower j)
  refine ⟨⟨B, hB⟩, c, hc, ?_, ?_⟩
  · intro k
    have hj : min (Nat.unpair i).1 k ∈ s :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let j := min (Nat.unpair i).1 k
    let l : Fin (N j + 1) := ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    have h := ((cover k j (min_le_right _ _)).unitBallMap_distances
      (hρ j) l x y).2
    change dist (diagonalUnitBallMap cover k i x) (diagonalUnitBallMap cover k i y) ≤
      B * dist x y
    exact (show dist (diagonalUnitBallMap cover k i x)
        (diagonalUnitBallMap cover k i y) ≤ upper (min (Nat.unpair i).1 k) * dist x y by
      simpa only [FlowCarrier.dist_metricSpaceOf, BasedFlow.metricAt,
        diagonalUnitBallMap, stageUnitBallMap, upper, j, l] using h).trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' upper hj) dist_nonneg)
  · intro k x y
    have hj : min (Nat.unpair i).1 k ∈ s :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le lower hj) dist_nonneg).trans
      ((cover k _ (min_le_right _ _)).unitBallMap_lower_distance_of_flow
        _ (hρ _) (ha _) x y)

theorem diagonalUnitBallMap_pairwise_bounded
    (L : ℕ → ℝ≥0) (hL : ∀ k i, LipschitzWith (L i) (diagonalUnitBallMap cover k i))
    (i j : ℕ) (x y : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ B : ℝ, ∀ k,
      dist (diagonalUnitBallMap cover k i x) (diagonalUnitBallMap cover k j y) ≤ B := by
  have hbase (i k : ℕ) (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
      dist (S.flow k).base (diagonalUnitBallMap cover k i x) ≤
        ((Nat.unpair i).1 : ℝ) + 1 + L i := by
    let q := min (Nat.unpair i).1 k
    let l : Fin (N q + 1) := ⟨(Nat.unpair i).2 % (N q + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    let z : ball (0 : EuclideanSpace ℝ (Fin n)) 1 := ⟨0, by simp⟩
    have hz : diagonalUnitBallMap cover k i z = (cover k q (min_le_right _ _)).centre l := by
      simp only [diagonalUnitBallMap, stageUnitBallMap, unitBallMap, z, smul_zero]
      exact (cover k q (min_le_right _ _)).map_zero l
    have hcentre : (cover k q (min_le_right _ _)).centre l ∈
        ball (S.flow k).base ((q : ℝ) + 1) := by
      rw [FlowCarrier.metricBall_eq_metricBallOf]
      exact (cover k q (min_le_right _ _)).centre_mem l
    have hx : dist z x ≤ 1 := by
      simpa only [Subtype.dist_eq, z, dist_zero_left] using
        (mem_ball_zero_iff.mp x.property).le
    calc
      dist (S.flow k).base (diagonalUnitBallMap cover k i x) ≤
          dist (S.flow k).base (diagonalUnitBallMap cover k i z) +
            dist (diagonalUnitBallMap cover k i z) (diagonalUnitBallMap cover k i x) :=
        dist_triangle _ _ _
      _ ≤ ((q : ℝ) + 1) + L i := by
        apply add_le_add
        · rw [hz, dist_comm]
          exact (mem_ball.mp hcentre).le
        · exact ((hL k i).dist_le_mul z x).trans
            (by simpa using mul_le_mul_of_nonneg_left hx (L i).coe_nonneg)
      _ ≤ ((Nat.unpair i).1 : ℝ) + 1 + L i := by
        have hq : (q : ℝ) ≤ ((Nat.unpair i).1 : ℝ) := by
          exact_mod_cast min_le_left (Nat.unpair i).1 k
        linarith
  refine ⟨(((Nat.unpair i).1 : ℝ) + 1 + L i) + (((Nat.unpair j).1 : ℝ) + 1 + L j), ?_⟩
  intro k
  calc
    dist (diagonalUnitBallMap cover k i x) (diagonalUnitBallMap cover k j y) ≤
        dist (S.flow k).base (diagonalUnitBallMap cover k i x) +
          dist (S.flow k).base (diagonalUnitBallMap cover k j y) := dist_triangle_left _ _ _
    _ ≤ _ := add_le_add (hbase i k x) (hbase j k y)

theorem diagonalUnitBallMap_compact_cover (hρ : ∀ j, 0 < ρ j) :
    ∀ A : ℝ, 0 < A → ∃ s : Finset ℕ,
      ∃ K : ℕ → Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ i ∈ s, IsCompact (K i)) ∧
          ∀ᶠ k in atTop, ball (S.flow k).base A ⊆
            ⋃ i ∈ s, diagonalUnitBallMap cover k i '' K i := by
  classical
  intro A _hA
  obtain ⟨j, hj⟩ := exists_nat_gt A
  let K : Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {x | ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himage : Subtype.val '' K = closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_closedBall_zero_iff.mpr hy
      · intro hx
        refine ⟨⟨x, mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num))⟩,
          mem_closedBall_zero_iff.mp hx, rfl⟩
    rw [himage]
    exact isCompact_closedBall _ _
  let s := Finset.univ.image (fun l : Fin (N j + 1) => Nat.pair j l)
  refine ⟨s, fun _ => K, fun _ _ => hK, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk
  intro y hy
  have hy' : y ∈ ((S.flow k).flow.metric 0).ball (S.flow k).base ((j : ℝ) + 1) := by
    have h := (ball_subset_ball (show A ≤ (j : ℝ) + 1 by linarith)) hy
    rw [FlowCarrier.metricBall_eq_metricBallOf] at h
    exact h
  obtain ⟨l, x, hx, hxy⟩ := mem_iUnion.mp ((cover k j hk).unitBallMap_cover (hρ j) hy')
  refine mem_iUnion.mpr ⟨Nat.pair j l, mem_iUnion.mpr ⟨Finset.mem_image.mpr
    ⟨l, Finset.mem_univ _, rfl⟩, ?_⟩⟩
  refine ⟨x, hx, ?_⟩
  rw [diagonalUnitBallMap_pair cover k j hk l]
  exact hxy

end PoincareConjecture.NormalChartCover
