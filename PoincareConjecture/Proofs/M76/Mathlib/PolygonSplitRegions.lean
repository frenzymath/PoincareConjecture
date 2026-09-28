import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitIntersection
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitIndex
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionPartition











set_option autoImplicit false

open Set

namespace Polygon

variable {m n : ℕ}



theorem hasNonverticalEdges_split (u : Fin (m + 1) → ℝ × ℝ)
    (v : Fin (n + 1) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasNonverticalEdges) (hd : (u 0).1 ≠ (v 0).1) :
    (mk (Fin.snoc u (v 0))).HasNonverticalEdges ∧
      (mk (Fin.snoc v (u 0))).HasNonverticalEdges := by
  constructor
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [finRotate_last, Fin.snoc_last, Fin.snoc_apply_zero] using hd.symm
    | cast i =>
      have hrot : finRotate ((m + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      simpa only [hrot, Fin.snoc_castSucc, Fin.append_left, Fin.append_finRotate_castAdd] using
        hP (i.castAdd (n + 1))
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [finRotate_last, Fin.snoc_last, Fin.snoc_apply_zero] using hd
    | cast i =>
      have hrot : finRotate ((n + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      simpa only [hrot, Fin.snoc_castSucc, Fin.append_right, Fin.append_finRotate_natAdd] using
        hP (Fin.natAdd (m + 1) i)





theorem region_partition_split_of_nonvertical (u : Fin (m + 2) → ℝ × ℝ)
    (v : Fin (n + 2) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hvP : (mk (Fin.append u v)).HasNonverticalEdges)
    (hdv : (u 0).1 ≠ (v 0).1)
    (hdiagonal : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside) :
    Disjoint (mk (Fin.snoc u (v 0))).inside (mk (Fin.snoc v (u 0))).inside ∧
      closure (mk (Fin.append u v)).inside =
        closure (mk (Fin.snoc u (v 0))).inside ∪ closure (mk (Fin.snoc v (u 0))).inside ∧
      closure (mk (Fin.snoc u (v 0))).inside ∩ closure (mk (Fin.snoc v (u 0))).inside =
        segment ℝ (u 0) (v 0) := by
  have hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆ {u 0, v 0} := by
    rintro x ⟨hx, hxb⟩
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · simp
    · simp
    · exact ((hdiagonal hx).1 hxb).elim
  have hs := hasSimplicialEdges_split u v hP hinj hchord
  have hi := injective_split u v hinj
  have hv := hasNonverticalEdges_split u v hvP hdv
  have hfront : frontier (mk (Fin.append u v)).inside = (mk (Fin.append u v)).boundary ℝ := by
    cases n <;> exact frontier_inside _ hP hinj
  have hb : (mk (Fin.append u v)).boundary ℝ ⊆ closure (mk (Fin.append u v)).inside := by
    rw [← hfront]
    exact frontier_subset_closure
  have hvertex (i) : (Fin.append u v) i ∈ (mk (Fin.append u v)).boundary ℝ := by
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [edgeSet, affineSegment_eq_segment]
    exact left_mem_segment ℝ _ _
  have hu : u 0 ∈ (mk (Fin.append u v)).boundary ℝ := by
    simpa only [Fin.append_left] using hvertex ((0 : Fin (m + 2)).castAdd (n + 2))
  have hv0 : v 0 ∈ (mk (Fin.append u v)).boundary ℝ := by
    simpa only [Fin.append_right] using hvertex (Fin.natAdd (m + 2) (0 : Fin (n + 2)))
  have hd : segment ℝ (u 0) (v 0) ⊆ closure (mk (Fin.append u v)).inside := by
    rw [← insert_endpoints_openSegment]
    exact insert_subset (hb hu) (insert_subset (hb hv0) (hdiagonal.trans subset_closure))
  have hboth : (mk (Fin.snoc u (v 0))).boundary ℝ ∪ (mk (Fin.snoc v (u 0))).boundary ℝ ⊆
      closure (mk (Fin.append u v)).inside := by
    rw [boundary_split_union]
    exact union_subset hb hd
  have hcover : (mk (Fin.append u v)).boundary ℝ ⊆
      (mk (Fin.snoc u (v 0))).boundary ℝ ∪ (mk (Fin.snoc v (u 0))).boundary ℝ := by
    rw [boundary_split_union]
    exact subset_union_left
  have hpartition :
      Disjoint (mk (Fin.snoc u (v 0))).inside (mk (Fin.snoc v (u 0))).inside ∧
      closure (mk (Fin.append u v)).inside =
        closure (mk (Fin.snoc u (v 0))).inside ∪ closure (mk (Fin.snoc v (u 0))).inside := by
    cases n <;>
      exact region_partition_of_index_sum _ _ _ hP hinj hvP hs.1 hi.1 hv.1 hs.2 hi.2 hv.2
        (fun _ hx => hboth (Or.inl hx)) (fun _ hx => hboth (Or.inr hx)) hcover
        (crossingIndex_append_split u v)
  refine ⟨hpartition.1, hpartition.2, ?_⟩
  rw [closure_inside_inter_eq_boundary_inter _ _ hs.1 hi.1 hs.2 hi.2 hpartition.1]
  exact boundary_split_inter u v hP hinj hchord

end Polygon
