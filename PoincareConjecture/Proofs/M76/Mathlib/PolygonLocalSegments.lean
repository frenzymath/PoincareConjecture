import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges
import PoincareConjecture.Proofs.M76.Mathlib.SegmentSubdivision

set_option autoImplicit false

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Wbtw.segment_inter_eq_endpoint {a q b : E} (h : Wbtw ℝ a q b) :
    segment ℝ a q ∩ segment ℝ q b = {q} := by
  by_cases hab : a = b
  · have hq : q = a := by simpa only [hab, wbtw_self_iff] using h
    simp [hab, hq]
  obtain ⟨t, ht, rfl⟩ := h
  have hl : segment ℝ a (AffineMap.lineMap a b t) =
      AffineMap.lineMap a b '' Icc (0 : ℝ) t := by
    rw [← segment_eq_Icc ht.1, image_segment]
    simp only [AffineMap.lineMap_apply_zero]
  have hr : segment ℝ (AffineMap.lineMap a b t) b =
      AffineMap.lineMap a b '' Icc t (1 : ℝ) := by
    rw [← segment_eq_Icc ht.2, image_segment]
    simp only [AffineMap.lineMap_apply_one]
  rw [hl, hr, ← image_inter (AffineMap.lineMap_injective ℝ hab)]
  have hi : Icc (0 : ℝ) t ∩ Icc t 1 = {t} := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
    constructor
    · exact fun hx => le_antisymm hx.1.2 hx.2.1
    · rintro rfl
      exact ⟨⟨ht.1, le_rfl⟩, ⟨le_rfl, ht.2⟩⟩
  rw [hi, image_singleton]

namespace Polygon

variable {n : ℕ}

theorem exists_local_segment_pair (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {q : E} (hq : q ∈ P.boundary ℝ) :
    ∃ u v : E, u ≠ q ∧ v ≠ q ∧
      segment ℝ q u ∩ segment ℝ q v = {q} ∧
      segment ℝ q u ∪ segment ℝ q v ⊆ P.boundary ℝ ∧
      ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔
        x ∈ segment ℝ q u ∪ segment ℝ q v := by
  by_cases hqv : q ∈ range P
  · obtain ⟨i, rfl⟩ := hqv
    have hn (j : Fin (n + 3)) : finRotate (n + 3) j ≠ j := by
      rw [finRotate_apply]
      intro h
      have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel
        (show j + 1 = j + 0 by simpa only [add_zero] using h)
      have hval := congrArg Fin.val h1
      change 1 % (n + 3) = 0 at hval
      rw [Nat.mod_eq_of_lt (by omega)] at hval
      exact Nat.one_ne_zero hval
    have hp : (finRotate (n + 3)).symm i ≠ i := by
      intro h
      exact hn i (by simpa only [Equiv.apply_symm_apply] using
        (congrArg (finRotate (n + 3)) h).symm)
    have he : P.edgeSet ℝ ((finRotate (n + 3)).symm i) =
        segment ℝ (P i) (P ((finRotate (n + 3)).symm i)) := by
      simp only [edgeSet, affineSegment_eq_segment, Equiv.apply_symm_apply]
      exact segment_symm _ _ _
    have hf : P.edgeSet ℝ i = segment ℝ (P i) (P (finRotate (n + 3) i)) :=
      affineSegment_eq_segment _ _ _
    refine ⟨_, _, hinj.ne hp, hinj.ne (hn i), ?_, ?_, ?_⟩
    · rw [← he, ← hf]
      simpa only [Equiv.apply_symm_apply] using
        P.adjacent_edgeSet_inter hP hinj ((finRotate (n + 3)).symm i)
    · rw [← he, ← hf]
      exact union_subset (subset_iUnion (fun j => P.edgeSet ℝ j) _)
        (subset_iUnion (fun j => P.edgeSet ℝ j) _)
    · simpa only [he, hf] using P.eventually_boundary_iff_adjacent_edges hP hinj i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    have hqi : Wbtw ℝ (P i) q (P (finRotate (n + 3) i)) := by
      apply mem_segment_iff_wbtw.mp
      simpa only [edgeSet, affineSegment_eq_segment] using hi
    have hsplit : segment ℝ q (P i) ∪ segment ℝ q (P (finRotate (n + 3) i)) =
        P.edgeSet ℝ i := by
      rw [segment_symm ℝ q (P i), hqi.segment_union]
      exact (affineSegment_eq_segment _ _ _).symm
    refine ⟨P i, P (finRotate (n + 3) i), fun h => hqv ⟨i, h⟩,
      fun h => hqv ⟨_, h⟩, ?_, ?_, ?_⟩
    · rw [segment_symm ℝ q (P i)]
      exact hqi.segment_inter_eq_endpoint
    · rw [hsplit]
      exact subset_iUnion (fun j => P.edgeSet ℝ j) i
    · rw [hsplit]
      exact P.eventually_boundary_iff_single_edge hP hinj hqv hi

end Polygon
