import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RescaledCharts
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ComponentDistances
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))

private noncomputable def regularStageUnitBallMap (k j : ℕ) (hjk : j ≤ k) (l : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M k :=
  (cover k j hjk).unitBallMap ⟨l % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ x

noncomputable def regularUnitBallMap (k i : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M k :=
  regularStageUnitBallMap cover k (min (Nat.unpair i).1 k) (min_le_right _ _)
    (Nat.unpair i).2 x

theorem regularUnitBallMap_of_le (k i : ℕ) (hik : (Nat.unpair i).1 ≤ k) :
    regularUnitBallMap cover k i =
      (cover k (Nat.unpair i).1 hik).unitBallMap
        ⟨(Nat.unpair i).2 % (N (Nat.unpair i).1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  funext x
  simp only [regularUnitBallMap, min_eq_left hik]
  rfl

theorem regularUnitBallMap_pair (k j : ℕ) (hjk : j ≤ k) (l : Fin (N j + 1)) :
    regularUnitBallMap cover k (Nat.pair j l) = (cover k j hjk).unitBallMap l := by
  funext x
  simp only [regularUnitBallMap, Nat.unpair_pair, min_eq_left hjk]
  simp only [regularStageUnitBallMap, Nat.mod_eq_of_lt l.isLt]

theorem regularUnitBallMap_zero (k : ℕ) :
    regularUnitBallMap cover k 0 ⟨0, by simp⟩ = p k := by
  change regularUnitBallMap cover k (Nat.pair 0 (0 : Fin (N 0 + 1))) ⟨0, by simp⟩ = _
  rw [regularUnitBallMap_pair cover k 0 (Nat.zero_le k) (0 : Fin (N 0 + 1))]
  simp only [RegularNormalChartCover.unitBallMap, smul_zero]
  exact ((cover k 0 (Nat.zero_le k)).map_zero 0).trans
    (cover k 0 (Nat.zero_le k)).centre_zero

theorem regularUnitBallMap_isLocalDiffeomorph
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    letI : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n))
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (regularUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isLocalDiffeomorph (hρ _) (hρR _) _

theorem regularUnitBallMap_isOpenEmbedding
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    Topology.IsOpenEmbedding (regularUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isOpenEmbedding (hρ _) (hρR _) _

theorem regularUnitBallMap_distance_bounds
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hρ : ∀ j, 0 < ρ j) (i : ℕ) :
    ∃ L : ℝ≥0, ∃ c : ℝ, 0 < c ∧
      (∀ k, LipschitzWith L (regularUnitBallMap cover k i)) ∧
      ∀ k x y, c * dist x y ≤
        dist (regularUnitBallMap cover k i x) (regularUnitBallMap cover k i y) := by
  classical
  let S := Finset.range ((Nat.unpair i).1 + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  let upper := fun j => Real.sqrt (9 / 4 : ℝ) * (ρ j / 2)
  let lower := fun j => Real.sqrt (1 / 4 : ℝ) * (ρ j / 2)
  have hupper (j : ℕ) : 0 ≤ upper j :=
    mul_nonneg (Real.sqrt_nonneg _) (half_pos (hρ j)).le
  have hlower (j : ℕ) : 0 < lower j :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) (half_pos (hρ j))
  let B := S.sup' hS upper
  have hB : 0 ≤ B := (hupper 0).trans (Finset.le_sup' upper (by simp [S]))
  let c := S.inf' hS lower
  have hc : 0 < c := (Finset.lt_inf'_iff hS).2 (fun j _ => hlower j)
  have hreal (k : ℕ) (x y : M k) : ((g k).edist x y).toReal = dist x y := by
    rw [← hdist, ← dist_edist]
  refine ⟨⟨B, hB⟩, c, hc, ?_, ?_⟩
  · intro k
    have hj : min (Nat.unpair i).1 k ∈ S :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := ((cover k _ (min_le_right _ _)).unitBallMap_distances
      (hρ _) ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ x y).2
    rw [hreal] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Finset.le_sup' upper hj) dist_nonneg)
  · intro k x y
    have hj : min (Nat.unpair i).1 k ∈ S :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    have h := ((cover k _ (min_le_right _ _)).unitBallMap_distances
      (hρ _) ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ x y).1
    rw [hreal] at h
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le lower hj) dist_nonneg).trans h

theorem regularUnitBallMap_base_distance_bound
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j) (i : ℕ) :
    ∃ B : ℝ, ∀ k x, dist (p k) (regularUnitBallMap cover k i x) ≤ B := by
  classical
  let S := Finset.range ((Nat.unpair i).1 + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  let bound := fun j => (ρ j / 2) * (N j + 1 : ℕ) + ρ j / 2
  refine ⟨S.sup' hS bound, ?_⟩
  intro k x
  have hj : min (Nat.unpair i).1 k ∈ S :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
  have h := (cover k _ (min_le_right _ _)).chart_distance_le (hdist k) (hρ _) (hρR _)
    ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩ (NormalChartCover.rescale_mem_half_ball (hρ _) x)
  exact h.trans (Finset.le_sup' bound hj)

theorem regularUnitBallMap_pairwise_bounded
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j)
    (i j : ℕ) :
    ∃ B : ℝ, ∀ k x y,
      dist (regularUnitBallMap cover k i x) (regularUnitBallMap cover k j y) ≤ B := by
  obtain ⟨A, hA⟩ := regularUnitBallMap_base_distance_bound cover hdist hρ hρR i
  obtain ⟨B, hB⟩ := regularUnitBallMap_base_distance_bound cover hdist hρ hρR j
  exact ⟨A + B, fun k x y => (dist_triangle_left _ _ (p k)).trans
    (add_le_add (hA k x) (hB k y))⟩

theorem regularUnitBallMap_eventually_mem_regularComponent
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (i : ℕ) :
    ∀ᶠ k in atTop, ∀ x,
      regularUnitBallMap cover k i x ∈
        regularComponent (g k) (p k) (2 * δ (Nat.unpair i).1) := by
  filter_upwards [eventually_ge_atTop (Nat.unpair i).1] with k hk x
  rw [regularUnitBallMap_of_le cover k i hk]
  exact (cover k _ hk).unitBallMap_mem_regularComponent (hρ _) (hρR _) _ x

theorem regularUnitBallMap_compact_cover (hρ : ∀ j, 0 < ρ j) (j : ℕ) :
    ∃ S : Finset ℕ,
      ∃ K : ℕ → Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ i ∈ S, IsCompact (K i)) ∧
          ∀ᶠ k in atTop, regularComponent (g k) (p k) (4 * δ j) ⊆
            ⋃ i ∈ S, regularUnitBallMap cover k i '' K i := by
  classical
  let K : Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {x | ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 4}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himage : Subtype.val '' K = closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 4) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_closedBall_zero_iff.mpr hy
      · intro hx
        refine ⟨⟨x, mem_ball_zero_iff.mpr
          ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num))⟩,
          mem_closedBall_zero_iff.mp hx, rfl⟩
    rw [himage]
    exact isCompact_closedBall _ _
  let S := Finset.univ.image (fun l : Fin (N j + 1) => Nat.pair j l)
  refine ⟨S, fun _ => K, fun _ _ => hK, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk
  intro y hy
  obtain ⟨l, x, hx, hxy⟩ := mem_iUnion.mp ((cover k j hk).unitBallMap_cover (hρ j) hy)
  refine mem_iUnion₂.mpr ⟨Nat.pair j l, Finset.mem_image.mpr
    ⟨l, Finset.mem_univ _, rfl⟩, x, hx, ?_⟩
  rw [regularUnitBallMap_pair cover k j hk l]
  exact hxy

end PoincareConjecture.M28
