import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevelUniqueness

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem convexHull_insert_inter_nonneg_of_zero (A : E →ᵃ[ℝ] ℝ)
    {q : E} (hq : A q = 0) (s : Set E) :
    convexHull ℝ (insert q s) ∩ {x | 0 ≤ A x} =
      convexHull ℝ (insert q (convexHull ℝ s ∩ {x | 0 ≤ A x})) := by
  by_cases hs : s.Nonempty
  · apply Subset.antisymm
    · rintro x ⟨hx, hAx⟩
      rw [convexHull_insert hs] at hx
      obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx
      have haq : a = q := mem_singleton_iff.mp ha
      subst a
      rw [segment_eq_image_lineMap] at hxy
      obtain ⟨t, ht, rfl⟩ := hxy
      change 0 ≤ A (lineMap q y t) at hAx
      have hz : 0 ≤ t * A y := by
        simpa only [A.apply_lineMap, hq, lineMap_apply_ring', sub_zero, add_zero] using hAx
      by_cases ht0 : t = 0
      · subst t
        simpa only [lineMap_apply_zero] using
          subset_convexHull ℝ _ (mem_insert q (convexHull ℝ s ∩ {x | 0 ≤ A x}))
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (fun h => ht0 h.symm)
        have hy0 : 0 ≤ A y := (mul_nonneg_iff_of_pos_left htpos).mp hz
        exact (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (mem_insert _ _))
          (subset_convexHull ℝ _ (mem_insert_of_mem q
            (show y ∈ convexHull ℝ s ∩ {x | 0 ≤ A x} from ⟨hy, hy0⟩)))
          (lineMap_mem_segment ℝ q y ht)
    · apply convexHull_min
      · intro x hx
        rcases mem_insert_iff.mp hx with rfl | hx
        · exact ⟨subset_convexHull ℝ _ (mem_insert _ _), hq.ge⟩
        · exact ⟨convexHull_mono (subset_insert q s) hx.1, hx.2⟩
      · exact (convex_convexHull ℝ _).inter ((convex_Ici (0 : ℝ)).affine_preimage A)
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [hs0, convexHull_empty, empty_inter, insert_empty_eq, convexHull_singleton]
    ext x
    constructor
    · exact fun hx => hx.1
    · rintro rfl
      exact ⟨mem_singleton _, hq.ge⟩

theorem convexHull_pair_inter_nonneg (A : E →ᵃ[ℝ] ℝ) {u v : E}
    (hu : A u < 0) (hv : 0 < A v) :
    convexHull ℝ ({u, v} : Set E) ∩ {x | 0 ≤ A x} =
      segment ℝ (A.zeroCrossing u v) v := by
  let w := A.zeroCrossing u v
  have hw : A w = 0 := A.zeroCrossing_apply (hu.trans hv).ne
  have hwseg : w ∈ segment ℝ u v :=
    openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment hu hv)
  have hwspan : w ∈ affineSpan ℝ ({u, v} : Set E) :=
    convexHull_subset_affineSpan _ (by rwa [convexHull_pair])
  have hwv : w ≠ v := fun h => hv.ne' (h ▸ hw)
  have hlines : affineSpan ℝ ({w, v} : Set E) = affineSpan ℝ ({u, v} : Set E) :=
    affineSpan_pair_eq_of_left_mem_of_ne hwspan hwv
  apply Subset.antisymm
  · rintro x ⟨hx, hx0⟩
    have hverts : ({u, v} : Set E) ⊆ {z | A z ≤ A v} := by
      intro z hz
      change A z ≤ A v
      rcases mem_insert_iff.mp hz with hz | hz
      · rw [hz]
        exact (hu.trans hv).le
      · rw [mem_singleton_iff.mp hz]
    have hupper : convexHull ℝ ({u, v} : Set E) ⊆ {z | A z ≤ A v} :=
      convexHull_min hverts ((convex_Iic (A v)).affine_preimage A)
    have hxv : A x ≤ A v := hupper hx
    have hxline : x ∈ affineSpan ℝ ({w, v} : Set E) := by
      rw [hlines]
      exact convexHull_subset_affineSpan _ hx
    have heq := A.eq_edgeLevel_of_mem_affineSpan (show A v ≠ A w by rw [hw]; exact hv.ne')
      hxline rfl
    rw [heq, edgeLevel_eq_lineMap, hw]
    simp only [sub_zero]
    exact lineMap_mem_segment ℝ w v
      ⟨div_nonneg hx0 hv.le, (div_le_one hv).mpr hxv⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [convexHull_pair]
      exact (convex_segment u v).segment_subset hwseg (right_mem_segment ℝ u v) hx
    · have hnonneg : convexHull ℝ ({w, v} : Set E) ⊆ {x | 0 ≤ A x} :=
        convexHull_min (by
          rintro z (rfl | rfl)
          · exact hw.ge
          · exact hv.le)
          ((convex_Ici (0 : ℝ)).affine_preimage A)
      exact hnonneg (by rwa [convexHull_pair])

theorem convexHull_zero_apex_pair_inter_nonneg (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) (hv : 0 < A v) :
    convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | 0 ≤ A x} =
      convexHull ℝ (insert q ({A.zeroCrossing u v, v} : Set E)) := by
  rw [A.convexHull_insert_inter_nonneg_of_zero hq, A.convexHull_pair_inter_nonneg hu hv,
    ← convexHull_pair, insert_eq, convexHull_convexHull_union_right]
  rfl

end AffineMap
