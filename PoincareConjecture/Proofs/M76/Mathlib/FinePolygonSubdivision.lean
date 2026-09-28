import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity
import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Affine.AddTorsor










set_option autoImplicit false

open Set Metric AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}




theorem exists_subdivision_short_edges (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      ∀ i, dist (Q i) (Q (finRotate (N + 3) i)) < δ := by
  let D : ℝ := ∑ i : Fin (n + 3), dist (P i) (P (finRotate (n + 3) i))
  obtain ⟨m, hm⟩ := exists_nat_gt (D / δ)
  have hden : 0 < (m + 1 : ℝ) := by positivity
  have hsmall : D / (m + 1 : ℝ) < δ := by
    apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ hδ).mp hm
    nlinarith
  let t : Fin (m + 2) → ℝ := fun i => (i.val : ℝ) / (m + 1 : ℝ)
  have ht : StrictMono t := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right hden).mpr (by exact_mod_cast hij)
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t (Fin.last (m + 1)) = 1 := by
    simp [t, Nat.cast_add, Nat.cast_one, hden.ne']
  have hstep (j : Fin (m + 1)) : dist (t j.castSucc) (t j.succ) = 1 / (m + 1 : ℝ) := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (ht Fin.castSucc_lt_succ).le)]
    dsimp [t]
    push_cast
    ring
  let R := P.subdivide t
  have hRi := P.injective_subdivide hP hinj t ht ht0 ht1
  have hRs := P.hasSimplicialEdges_subdivide hP hinj t ht ht0 ht1
  have hRb := P.subdivide_boundary t ht ht0 ht1
  have hRd (k : Fin ((n + 3) * (m + 1))) :
      dist (R k) (R (finRotate ((n + 3) * (m + 1)) k)) < δ := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    change dist (P.subdivide t (finProdFinEquiv (i, j)))
      (P.subdivide t (finRotate ((n + 3) * (m + 1)) (finProdFinEquiv (i, j)))) < δ
    rw [P.subdivide_apply, P.subdivide_rotate_apply t ht0 ht1,
      dist_lineMap_lineMap, hstep]
    have hbound : dist (P i) (P (finRotate (n + 3) i)) ≤ D := by
      exact Finset.single_le_sum
        (f := fun j => dist (P j) (P (finRotate (n + 3) j)))
        (fun j _ => dist_nonneg) (Finset.mem_univ i)
    calc
      1 / (m + 1 : ℝ) * dist (P i) (P (finRotate (n + 3) i)) ≤
          1 / (m + 1 : ℝ) * D :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D / (m + 1 : ℝ) := by ring
      _ < δ := hsmall
  have hex : ∃ Q : Polygon E ((n + 3) * (m + 1)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      ∀ i, dist (Q i) (Q (finRotate ((n + 3) * (m + 1)) i)) < δ :=
    ⟨R, hRs, hRi, hRb, hRd⟩
  refine ⟨(n + 3) * m + n, ?_⟩
  have hN : (n + 3) * (m + 1) = ((n + 3) * m + n) + 3 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact hN ▸ hex





theorem exists_subdivision_subordinate_adjacent_edges
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {ι : Type*} (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : P.boundary ℝ ⊆ ⋃ i, U i) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)), Q.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.boundary ℝ = P.boundary ℝ ∧
      ∀ i, ∃ j, Q.edgeSet ℝ i ∪ Q.edgeSet ℝ (finRotate (N + 3) i) ⊆ U j := by
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric P.isCompact_boundary hU hcover
  obtain ⟨N, Q, hQ, hQi, hQP, hshort⟩ := P.exists_subdivision_short_edges hP hinj hδ
  refine ⟨N, Q, hQ, hQi, hQP, fun i => ?_⟩
  let j := finRotate (N + 3) i
  have hj : Q j ∈ P.boundary ℝ := by
    rw [← hQP]
    exact mem_iUnion.mpr ⟨j, 0, ⟨le_rfl, zero_le_one⟩, lineMap_apply_zero _ _⟩
  obtain ⟨k, hk⟩ := hLeb (Q j) hj
  refine ⟨k, (union_subset ?_ ?_).trans hk⟩
  · change affineSegment ℝ (Q i) (Q j) ⊆ ball (Q j) δ
    rw [affineSegment_eq_segment]
    exact (convex_ball (Q j) δ).segment_subset
      (show Q i ∈ ball (Q j) δ from hshort i) (mem_ball_self hδ)
  · change affineSegment ℝ (Q j) (Q (finRotate (N + 3) j)) ⊆ ball (Q j) δ
    rw [affineSegment_eq_segment]
    exact (convex_ball (Q j) δ).segment_subset (mem_ball_self hδ)
      (show Q (finRotate (N + 3) j) ∈ ball (Q j) δ by
        rw [mem_ball, dist_comm]
        exact hshort j)

end Polygon
