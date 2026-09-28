import PoincareConjecture.Proofs.M76.Mathlib.CyclicEdgeSums
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}

theorem edgeVertices_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (m + 1)) :
    (mk (Fin.snoc u (v 0))).edgeVertices i.castSucc =
      (mk (Fin.append u v)).edgeVertices (i.castAdd (n + 1)) := by
  classical
  have hrot : finRotate ((m + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simp only [edgeVertices, hrot, Fin.snoc_castSucc,
    Fin.append_left, Fin.append_finRotate_castAdd]

theorem edgeVertices_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) :
    (mk (Fin.snoc v (u 0))).edgeVertices i.castSucc =
      (mk (Fin.append u v)).edgeVertices (Fin.natAdd (m + 1) i) := by
  classical
  have hrot : finRotate ((n + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simp only [edgeVertices, hrot, Fin.snoc_castSucc,
    Fin.append_right, Fin.append_finRotate_natAdd]

theorem edgeVertices_snoc_last (u : Fin (m + 1) → E) (z : E) :
    ((mk (Fin.snoc u z)).edgeVertices (Fin.last (m + 1)) : Set E) = {z, u 0} := by
  classical
  simp [edgeVertices]

variable [AddCommGroup E] [Module ℝ E]

theorem edgeSet_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (m + 1)) :
    (mk (Fin.snoc u (v 0))).edgeSet ℝ i.castSucc =
      (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1)) := by
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull, edgeVertices_split_left]

theorem edgeSet_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) :
    (mk (Fin.snoc v (u 0))).edgeSet ℝ i.castSucc =
      (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i) := by
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull, edgeVertices_split_right]

theorem edgeSet_snoc_last (u : Fin (m + 1) → E) (z : E) :
    (mk (Fin.snoc u z)).edgeSet ℝ (Fin.last (m + 1)) = segment ℝ z (u 0) := by
  rw [edgeSet_eq_convexHull, edgeVertices_snoc_last, convexHull_pair]

theorem boundary_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc u (v 0))).boundary ℝ =
      (⋃ i : Fin (m + 1), (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1))) ∪
        segment ℝ (u 0) (v 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    induction i using Fin.lastCases with
    | last =>
      right
      rwa [edgeSet_snoc_last, segment_symm] at hi
    | cast i =>
      left
      exact mem_iUnion.mpr ⟨i, (edgeSet_split_left u v i) ▸ hi⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.castSucc, (edgeSet_split_left u v i).symm ▸ hi⟩
    · apply mem_iUnion.mpr
      refine ⟨Fin.last (m + 1), ?_⟩
      rwa [edgeSet_snoc_last, segment_symm]

theorem boundary_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc v (u 0))).boundary ℝ =
      (⋃ i : Fin (n + 1), (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i)) ∪
        segment ℝ (u 0) (v 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    induction i using Fin.lastCases with
    | last =>
      right
      rwa [edgeSet_snoc_last] at hi
    | cast i =>
      left
      exact mem_iUnion.mpr ⟨i, (edgeSet_split_right u v i) ▸ hi⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.castSucc, (edgeSet_split_right u v i).symm ▸ hi⟩
    · apply mem_iUnion.mpr
      refine ⟨Fin.last (n + 1), ?_⟩
      rwa [edgeSet_snoc_last]

theorem boundary_split_union (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc u (v 0))).boundary ℝ ∪ (mk (Fin.snoc v (u 0))).boundary ℝ =
      (mk (Fin.append u v)).boundary ℝ ∪ segment ℝ (u 0) (v 0) := by
  rw [boundary_split_left, boundary_split_right]
  have h :
      (⋃ i : Fin (m + 1), (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1))) ∪
        (⋃ i : Fin (n + 1), (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i)) =
      (mk (Fin.append u v)).boundary ℝ := by
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castAdd (n + 1), hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨Fin.natAdd (m + 1) i, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      induction i using Fin.addCases with
      | left i => exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
      | right i => exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
  rw [union_union_union_comm, union_self, h]

end Polygon
