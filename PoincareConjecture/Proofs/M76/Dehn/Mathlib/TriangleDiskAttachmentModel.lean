import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDiskModel
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskPartition











set_option autoImplicit false

open Set

namespace TriangleDiskModel



theorem isFinitePLBallPair_common_edge :
    IsFinitePLBallPair ℝ (segment ℝ ((0, 1) : ℝ × ℝ) (0, 0)) {(0, 1), (0, 0)} := by
  have h := isFinitePLBallPair_affine_interval zero_lt_one
    (ContinuousAffineMap.lineMap ((0, 1) : ℝ × ℝ) (0, 0))
    (AffineMap.lineMap_injective ℝ (by norm_num)).injOn
  simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h

private theorem common_edge_subset_right_frontier :
    segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ⊆
      frontier (convexHull ℝ (range rightTriangle)) := by
  rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
  intro x hx
  apply mem_iUnion.mpr
  exact ⟨2, by simpa [Polygon.edgeSet, rightTriangle, affineSegment_eq_segment] using hx⟩

private theorem common_edge_subset_left_frontier :
    segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ⊆
      frontier (convexHull ℝ (range leftTriangle)) := by
  rw [leftTriangle.frontier_convexHull_triangle independent_leftTriangle]
  intro x hx
  apply mem_iUnion.mpr
  exact ⟨2, by
    simpa [Polygon.edgeSet, leftTriangle, affineSegment_eq_segment, segment_symm] using hx⟩

private theorem common_edge_sdiff_endpoints :
    segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) \ {(0, 1), (0, 0)} =
      openSegment ℝ (0, 1) (0, 0) := by
  ext x
  simp only [mem_sdiff, mem_common_edge_iff, mem_open_common_edge_iff, mem_insert_iff,
    mem_singleton_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨hx, hy, hy'⟩, hne⟩
    refine ⟨hx, lt_of_le_of_ne hy ?_, lt_of_le_of_ne hy' ?_⟩
    · intro h
      exact hne (Or.inr ⟨hx, h.symm⟩)
    · intro h
      exact hne (Or.inl ⟨hx, h⟩)
  · rintro ⟨hx, hy, hy'⟩
    refine ⟨⟨hx, hy.le, hy'.le⟩, ?_⟩
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact (ne_of_lt hy') h
    · exact (ne_of_gt hy) h




theorem exists_disk_attachment_model :
    ∃ b c : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (range rightTriangle))
        (b ∪ segment ℝ (0, 1) (0, 0)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (convexHull ℝ (range leftTriangle))
        (c ∪ segment ℝ (0, 1) (0, 0)) ∧
      IsFinitePLBallPair ℝ b {(0, 1), (0, 0)} ∧
      IsFinitePLBallPair ℝ c {(0, 1), (0, 0)} ∧
      b ∩ segment ℝ (0, 1) (0, 0) = {(0, 1), (0, 0)} ∧
      c ∩ segment ℝ (0, 1) (0, 0) = {(0, 1), (0, 0)} ∧
      IsFinitePLBallPair (ℝ × ℝ)
        (convexHull ℝ (range rightTriangle) ∪ convexHull ℝ (range leftTriangle))
        (b ∪ c) := by
  have hR := rightTriangle.isFinitePLBallPair_convexHull_triangle independent_rightTriangle
  have hL := leftTriangle.isFinitePLBallPair_convexHull_triangle independent_leftTriangle
  have hW := wholeTriangle.isFinitePLBallPair_convexHull_triangle independent_wholeTriangle
  obtain ⟨b, hb, hIb, hiIb⟩ := hR.exists_boundary_arc_complement
    isFinitePLBallPair_common_edge common_edge_subset_right_frontier (by norm_num)
  obtain ⟨c, hc, hIc, hiIc⟩ := hL.exists_boundary_arc_complement
    isFinitePLBallPair_common_edge common_edge_subset_left_frontier (by norm_num)
  have hbR : b ⊆ convexHull ℝ (range rightTriangle) :=
    fun _ hx => hR.1 (hIb ▸ Or.inr hx)
  have hcL : c ⊆ convexHull ℝ (range leftTriangle) :=
    fun _ hx => hL.1 (hIc ▸ Or.inr hx)
  have hbmem (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (range rightTriangle)) :
      x ∈ b ↔ x ∈ frontier (convexHull ℝ (range wholeTriangle)) := by
    rw [frontier_membership.1 x hx, ← hIb, ← common_edge_sdiff_endpoints]
    have hends : x ∈ ({(0, 1), (0, 0)} : Set (ℝ × ℝ)) → x ∈ b := fun hx => hb.1 hx
    have hmeet : x ∈ segment ℝ (0, 1) (0, 0) → x ∈ b →
        x ∈ ({(0, 1), (0, 0)} : Set (ℝ × ℝ)) :=
      fun hi hb' => hiIb.subset ⟨hi, hb'⟩
    simp only [mem_union, mem_sdiff]
    tauto
  have hcmem (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (range leftTriangle)) :
      x ∈ c ↔ x ∈ frontier (convexHull ℝ (range wholeTriangle)) := by
    rw [frontier_membership.2 x hx, ← hIc, ← common_edge_sdiff_endpoints]
    have hends : x ∈ ({(0, 1), (0, 0)} : Set (ℝ × ℝ)) → x ∈ c := fun hx => hc.1 hx
    have hmeet : x ∈ segment ℝ (0, 1) (0, 0) → x ∈ c →
        x ∈ ({(0, 1), (0, 0)} : Set (ℝ × ℝ)) :=
      fun hi hc' => hiIc.subset ⟨hi, hc'⟩
    simp only [mem_union, mem_sdiff]
    tauto
  have hboundary : b ∪ c = frontier (convexHull ℝ (range wholeTriangle)) := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact (hbmem x (hbR hx)).mp hx
      · exact (hcmem x (hcL hx)).mp hx
    · intro x hx
      have hcarrier := hW.1 hx
      rw [← region_union] at hcarrier
      rcases hcarrier with hxr | hxl
      · exact Or.inl ((hbmem x hxr).mpr hx)
      · exact Or.inr ((hcmem x hxl).mpr hx)
  refine ⟨b, c, ?_, ?_, hb, hc, ?_, ?_, ?_⟩
  · rwa [union_comm, hIb]
  · rwa [union_comm, hIc]
  · rwa [inter_comm]
  · rwa [inter_comm]
  · rwa [region_union, hboundary]

end TriangleDiskModel
