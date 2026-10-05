import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonInteriorCutArcs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.RadialSegmentGerms

/-!
# Distinct rays of the original adjacent polygon cuts

The complete original cut segments meet exactly at their
common polygon vertex. Strict cuts at a zero vertex thus
have distinct normalized directions, including collinear
opposite edges. See Alexander 1924, pp. 6--8, Hudson 1969,
pp. 12--19 and M76 derivation 286an.
-/

set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Both original cut segments meet only at their shared
polygon vertex. Non-strict cut parameters and degenerate
subsegments are permitted. See Alexander pp. 6--8 and
M76 derivation 286an. -/
theorem adjacent_cut_segments_inter
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) (i : Fin (n + 3)) :
    segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t i) ∩
      segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t (finRotate (n + 3) i)) =
        {P (finRotate (n + 3) i)} := by
  have hleft : segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t i) ⊆
      P.edgeSet ℝ i := by
    change segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t i) ⊆
      affineSegment ℝ (P i) (P (finRotate (n + 3) i))
    rw [affineSegment_eq_segment]
    exact (convex_segment (𝕜 := ℝ) (P i) (P (finRotate (n + 3) i))).segment_subset
      (right_mem_segment ℝ (P i) (P (finRotate (n + 3) i)))
      (lineMap_mem_segment ℝ (P i) (P (finRotate (n + 3) i)) (ht i))
  have hright :
      segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t (finRotate (n + 3) i)) ⊆
        P.edgeSet ℝ (finRotate (n + 3) i) := by
    change segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t (finRotate (n + 3) i)) ⊆
      affineSegment ℝ (P (finRotate (n + 3) i))
        (P (finRotate (n + 3) (finRotate (n + 3) i)))
    rw [affineSegment_eq_segment]
    exact (convex_segment (𝕜 := ℝ) (P (finRotate (n + 3) i))
      (P (finRotate (n + 3) (finRotate (n + 3) i)))).segment_subset
      (left_mem_segment ℝ (P (finRotate (n + 3) i))
        (P (finRotate (n + 3) (finRotate (n + 3) i))))
      (lineMap_mem_segment ℝ (P (finRotate (n + 3) i))
        (P (finRotate (n + 3) (finRotate (n + 3) i))) (ht (finRotate (n + 3) i)))
  apply Subset.antisymm
  · exact (inter_subset_inter hleft hright).trans (P.adjacent_edgeSet_inter hP hinj i).subset
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- At the actual zero vertex, strict original adjacent cuts
have distinct normalized rays. No replacement directions or
separation hypothesis are needed. See Alexander pp. 6--8
and M76 derivation 286an. -/
theorem normalize_adjacent_cut_ne
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3))
    (hvertex : P (finRotate (n + 3) i) = 0) :
    NormedSpace.normalize (P.edgeCut t i) ≠
      NormedSpace.normalize (P.edgeCut t (finRotate (n + 3) i)) := by
  have hnonzero (k : Fin (n + 3)) : P.edgeCut t k ≠ 0 := by
    intro h
    exact P.edgeCut_notMem_range hP hinj t (ht k)
      ⟨finRotate (n + 3) i, hvertex.trans h.symm⟩
  apply NormedSpace.normalize_ne_of_segment_inter (hnonzero i)
    (hnonzero (finRotate (n + 3) i))
  have hinter := P.adjacent_cut_segments_inter hP hinj t
    (fun k => ⟨(ht k).1.le, (ht k).2.le⟩) i
  rw [hvertex] at hinter
  exact hinter.subset

end Polygon
