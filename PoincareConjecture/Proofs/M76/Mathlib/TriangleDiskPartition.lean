import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskRegions
import PoincareConjecture.Proofs.M76.Mathlib.FrontierPieceMembership










set_option autoImplicit false

open Set

namespace TriangleDiskModel



theorem open_common_edge_subset_interior : openSegment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ⊆
    interior (convexHull ℝ (range wholeTriangle)) := by
  let O : Set (ℝ × ℝ) := {x | 0 < x.2 ∧ x.1 + x.2 < 1 ∧ x.2 - x.1 < 1}
  have ho : IsOpen O := (isOpen_lt continuous_const continuous_snd).inter
    ((isOpen_lt (continuous_fst.add continuous_snd) continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_fst) continuous_const))
  have hs : O ⊆ convexHull ℝ (range wholeTriangle) := fun x hx =>
    (mem_whole_region_iff x).mpr ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩
  intro x hx
  apply interior_maximal hs ho
  obtain ⟨hx0, hy, hy'⟩ := (mem_open_common_edge_iff x).mp hx
  exact ⟨hy, by simpa [hx0] using hy', by simpa [hx0] using hy'⟩

private theorem right_frontier : frontier (convexHull ℝ (range rightTriangle)) =
    segment ℝ (0, 0) (1, 0) ∪ segment ℝ (1, 0) (0, 1) ∪ segment ℝ (0, 1) (0, 0) := by
  rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
  ext x
  simp [Polygon.boundary, Polygon.edgeSet, rightTriangle, Fin.exists_fin_succ,
    affineSegment_eq_segment, or_assoc]

private theorem left_frontier : frontier (convexHull ℝ (range leftTriangle)) =
    segment ℝ (0, 1) (-1, 0) ∪ segment ℝ (-1, 0) (0, 0) ∪ segment ℝ (0, 0) (0, 1) := by
  rw [leftTriangle.frontier_convexHull_triangle independent_leftTriangle]
  ext x
  simp [Polygon.boundary, Polygon.edgeSet, leftTriangle, Fin.exists_fin_succ,
    affineSegment_eq_segment, or_assoc]

private theorem whole_frontier : frontier (convexHull ℝ (range wholeTriangle)) =
    segment ℝ (-1, 0) (1, 0) ∪ segment ℝ (1, 0) (0, 1) ∪ segment ℝ (0, 1) (-1, 0) := by
  rw [wholeTriangle.frontier_convexHull_triangle independent_wholeTriangle]
  ext x
  simp [Polygon.boundary, Polygon.edgeSet, wholeTriangle, Fin.exists_fin_succ,
    affineSegment_eq_segment, or_assoc]

private theorem origin_mem_base : ((0, 0) : ℝ × ℝ) ∈ segment ℝ (-1, 0) (1, 0) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  ext <;> norm_num

private theorem common_edge_subset_frontier_union_open :
    segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ⊆
      frontier (convexHull ℝ (range wholeTriangle)) ∪ openSegment ℝ (0, 1) (0, 0) := by
  rw [whole_frontier, ← insert_endpoints_openSegment]
  rintro x (rfl | rfl | hx)
  · exact Or.inl (Or.inl (Or.inr (right_mem_segment ℝ _ _)))
  · exact Or.inl (Or.inl (Or.inl origin_mem_base))
  · exact Or.inr hx

private theorem right_frontier_subset : frontier (convexHull ℝ (range rightTriangle)) ⊆
    frontier (convexHull ℝ (range wholeTriangle)) ∪ openSegment ℝ (0, 1) (0, 0) := by
  rw [right_frontier]
  rintro x ((hx | hx) | hx)
  · left
    rw [whole_frontier]
    exact Or.inl (Or.inl ((convex_segment (𝕜 := ℝ) (-1, 0) (1, 0)).segment_subset
      origin_mem_base (right_mem_segment ℝ _ _) hx))
  · left
    rw [whole_frontier]
    exact Or.inl (Or.inr hx)
  · exact common_edge_subset_frontier_union_open hx

private theorem left_frontier_subset : frontier (convexHull ℝ (range leftTriangle)) ⊆
    frontier (convexHull ℝ (range wholeTriangle)) ∪ openSegment ℝ (0, 1) (0, 0) := by
  rw [left_frontier]
  rintro x ((hx | hx) | hx)
  · left
    rw [whole_frontier]
    exact Or.inr hx
  · left
    rw [whole_frontier]
    exact Or.inl (Or.inl ((convex_segment (𝕜 := ℝ) (-1, 0) (1, 0)).segment_subset
      (left_mem_segment ℝ _ _) origin_mem_base hx))
  · exact common_edge_subset_frontier_union_open (by rwa [segment_symm])




theorem frontier_membership :
    (∀ x ∈ convexHull ℝ (range rightTriangle),
      x ∈ frontier (convexHull ℝ (range wholeTriangle)) ↔
        x ∈ frontier (convexHull ℝ (range rightTriangle)) ∧ x ∉ openSegment ℝ (0, 1) (0, 0)) ∧
    (∀ x ∈ convexHull ℝ (range leftTriangle),
      x ∈ frontier (convexHull ℝ (range wholeTriangle)) ↔
        x ∈ frontier (convexHull ℝ (range leftTriangle)) ∧ x ∉ openSegment ℝ (0, 1) (0, 0)) := by
  have hR : convexHull ℝ (range rightTriangle) ⊆ convexHull ℝ (range wholeTriangle) := by
    rw [← region_union]
    exact subset_union_left
  have hL : convexHull ℝ (range leftTriangle) ⊆ convexHull ℝ (range wholeTriangle) := by
    rw [← region_union]
    exact subset_union_right
  exact ⟨fun _ hx => frontier_mem_iff_of_subset hR right_frontier_subset
    open_common_edge_subset_interior hx,
    fun _ hx => frontier_mem_iff_of_subset hL left_frontier_subset
      open_common_edge_subset_interior hx⟩

end TriangleDiskModel
