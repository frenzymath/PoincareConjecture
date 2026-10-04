import Mathlib.Analysis.Convex.Between
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Splitting a segment at a point between its endpoints

The two subsegments cover the original segment. Collinear
adjacent edges meeting only at their shared endpoint therefore
form a single segment. See Erickson, Simple Polygons, pp. 2--3
and M76 derivation 98.
-/

set_option autoImplicit false

open Set AffineMap

variable {R E : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E]

/-- Subdividing a segment at a point weakly between its endpoints
does not change its underlying set. See M76 derivation 98. -/
theorem Wbtw.segment_union {a b c : E} (h : Wbtw R a b c) :
    segment R a b ∪ segment R b c = segment R a c := by
  obtain ⟨t, ht, rfl⟩ := h
  have hsplit : segment R (0 : R) t ∪ segment R t 1 = Icc (0 : R) 1 := by
    rw [segment_eq_uIcc, segment_eq_uIcc, uIcc_of_le ht.1, uIcc_of_le ht.2]
    exact Icc_union_Icc_eq_Icc ht.1 ht.2
  calc
    segment R a (lineMap a c t) ∪ segment R (lineMap a c t) c =
        lineMap a c '' (segment R (0 : R) t ∪ segment R t 1) := by
      rw [image_union, image_segment, image_segment]
      simp
    _ = segment R a c := by rw [hsplit, segment_eq_image_lineMap]

/-- If two nondegenerate collinear segments meet only at their
shared endpoint, that endpoint lies strictly between the outer
ones. See Erickson pp. 2--3 and M76 derivation 98. -/
theorem Collinear.sbtw_of_segment_inter_subset {a b c : E}
    (h : Collinear R ({a, b, c} : Set E)) (hab : a ≠ b) (hcb : c ≠ b)
    (hinter : segment R a b ∩ segment R b c ⊆ {b}) : Sbtw R a b c := by
  refine ⟨?_, hab.symm, hcb.symm⟩
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact h
  · exact (hcb (hinter ⟨h.symm.mem_segment, right_mem_segment R b c⟩)).elim
  · exact (hab (hinter ⟨left_mem_segment R a b, h.symm.mem_segment⟩)).elim
