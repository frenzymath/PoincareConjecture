import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.AffineZeroCrossing
import Mathlib.Analysis.Convex.Join

/-!
# Slicing a cone through its zero-height apex

The zero slice retains the apex even when the base slice is
empty. This gives the exceptional triangle sections used in
Alexander 1924, pp. 6--8. See M76 derivation 146.
-/

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Intersecting a convex cone from a zero-height apex with the
zero plane is the convex hull of that apex and the base slice.
The base, and its slice, may be empty. No independence is needed.
See Alexander pp. 6--8 and M76 derivation 146. -/
theorem convexHull_insert_inter_zero_of_zero (A : E →ᵃ[ℝ] ℝ)
    {q : E} (hq : A q = 0) (s : Set E) :
    convexHull ℝ (insert q s) ∩ {x | A x = 0} =
      convexHull ℝ (insert q (convexHull ℝ s ∩ {x | A x = 0})) := by
  by_cases hs : s.Nonempty
  · apply Subset.antisymm
    · rintro x ⟨hx, hAx⟩
      rw [convexHull_insert hs] at hx
      obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx
      have haq : a = q := mem_singleton_iff.mp ha
      subst a
      rw [segment_eq_image_lineMap] at hxy
      obtain ⟨t, ht, rfl⟩ := hxy
      change A (lineMap q y t) = 0 at hAx
      have hz : t * A y = 0 := by
        simpa only [A.apply_lineMap, hq, lineMap_apply_ring', sub_zero, add_zero] using hAx
      rcases mul_eq_zero.mp hz with ht0 | hy0
      · subst t
        simpa only [lineMap_apply_zero] using
          (subset_convexHull ℝ _ (mem_insert q (convexHull ℝ s ∩ {x | A x = 0})))
      · exact (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (mem_insert _ _))
          (subset_convexHull ℝ _ (mem_insert_of_mem q
            (show y ∈ convexHull ℝ s ∩ {x | A x = 0} from ⟨hy, hy0⟩)))
          (lineMap_mem_segment ℝ q y ht)
    · apply convexHull_min
      · intro x hx
        rcases mem_insert_iff.mp hx with rfl | hx
        · exact ⟨subset_convexHull ℝ _ (mem_insert _ _), hq⟩
        · exact ⟨convexHull_mono (subset_insert q s) hx.1, hx.2⟩
      · exact (convex_convexHull ℝ _).inter ((convex_singleton (0 : ℝ)).affine_preimage A)
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [hs0, convexHull_empty, empty_inter, insert_empty_eq, convexHull_singleton]
    ext x
    constructor
    · exact fun hx => hx.1
    · rintro rfl
      exact ⟨mem_singleton _, hq⟩

end AffineMap
