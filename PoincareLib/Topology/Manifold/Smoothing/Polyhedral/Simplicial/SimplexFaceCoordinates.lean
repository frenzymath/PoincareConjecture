import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic

/-!
# Coordinate support of simplex faces

An affine basis identifies affine faces with vanishing coordinates.
For convex faces the remaining coordinates must be nonnegative.
See Cairns 1940, pp. 804--806 and M76 derivation 68.
-/

set_option autoImplicit false

open Set

namespace AffineBasis

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A coordinate omitted from an affine face vanishes on its
whole span. See Cairns pp. 804--806 and M76 derivation 68. -/
theorem coord_eq_zero_of_mem_affineSpan_image (b : AffineBasis ι ℝ E)
    {s : Set ι} {i : ι} (hi : i ∉ s) {x : E}
    (hx : x ∈ affineSpan ℝ (b '' s)) : b.coord i x = 0 := by
  refine affineSpan_induction hx ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩
    exact b.coord_apply_ne (fun h => hi (h.symm ▸ hj))
  · intro c u v w hu hv hw
    rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
    simp only [hu, hv, hw, vsub_self, smul_zero, zero_vadd]

/-- Coordinate support exactly characterizes the affine span
of any subfamily of a finite affine basis. See Cairns pp. 804--806
and M76 derivation 68. -/
theorem mem_affineSpan_image_iff_coord_eq_zero [Finite ι]
    (b : AffineBasis ι ℝ E) (s : Set ι) (x : E) :
    x ∈ affineSpan ℝ (b '' s) ↔ ∀ i, i ∉ s → b.coord i x = 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · exact fun hx i hi => b.coord_eq_zero_of_mem_affineSpan_image hi hx
  · intro hx
    simpa only [b.affineCombination_coord_eq_self] using
      affineCombination_mem_affineSpan_image (b.sum_coord_apply_eq_one x)
        (fun i _ hi => hx i hi) b

/-- Nonnegative coordinates with the prescribed support exactly
characterize a convex face. See Cairns pp. 804--806 and M76
derivation 68. -/
theorem mem_convexHull_image_iff_coord [Finite ι]
    (b : AffineBasis ι ℝ E) (s : Set ι) (x : E) :
    x ∈ convexHull ℝ (b '' s) ↔
      (∀ i, 0 ≤ b.coord i x) ∧ (∀ i, i ∉ s → b.coord i x = 0) := by
  classical
  constructor
  · intro hx
    have hxfull := convexHull_mono (image_subset_range b s) hx
    rw [b.convexHull_eq_nonneg_coord] at hxfull
    exact ⟨hxfull, fun i hi => b.coord_eq_zero_of_mem_affineSpan_image hi
      (convexHull_subset_affineSpan _ hx)⟩
  · rintro ⟨hnonneg, hzero⟩
    obtain ⟨t, w, ht, hw, hcomb⟩ := eq_affineCombination_of_mem_affineSpan_image
      ((b.mem_affineSpan_image_iff_coord_eq_zero s x).mpr hzero)
    rw [hcomb, affineCombination_eq_centerMass hw]
    apply t.centerMass_mem_convexHull
    · intro i hi
      simpa only [hcomb, b.coord_apply_combination_of_mem hi hw] using hnonneg i
    · rw [hw]
      exact one_pos
    · intro i hi
      exact mem_image_of_mem b (ht hi)

end AffineBasis
