import PoincareConjecture.Proofs.M76.Mathlib.SimplexFaceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option autoImplicit false

open Set

namespace AffineBasis

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coord_pos_of_mem_intrinsicInterior_convexHull_image (b : AffineBasis ι ℝ E)
    {s : Set ι} {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (b '' s)))
    {j : ι} (hj : j ∈ s) : 0 < b.coord j x := by
  have hxC := intrinsicInterior_subset hx
  have hjC := subset_convexHull ℝ (b '' s) (mem_image_of_mem b hj)
  have hnonneg := ((b.mem_convexHull_image_iff_coord s x).mp hxC).1 j
  by_contra hpos
  have hzero : b.coord j x = 0 := le_antisymm (not_lt.mp hpos) hnonneg
  have hl : x - b j ∈ (affineSpan ℝ (convexHull ℝ (b '' s))).direction :=
    (affineSpan ℝ _).vsub_mem_direction (subset_affineSpan ℝ _ hxC)
      (subset_affineSpan ℝ _ hjC)
  obtain ⟨r, hr, hmove⟩ := Set.exists_pos_smul_add_mem_of_intrinsicInterior hx hl
  have hmove0 := ((b.mem_convexHull_image_iff_coord s _).mp hmove).1 j
  have he : b.coord j (r • (x - b j) + x) = -r := by
    change b.coord j (r • (x -ᵥ b j) +ᵥ x) = -r
    rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub, hzero, b.coord_apply_eq]
    simp
  rw [he] at hmove0
  linarith

theorem mem_interior_convexHull_of_mem_intrinsicInterior (b : AffineBasis ι ℝ E)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (range b))) :
    x ∈ interior (convexHull ℝ (range b)) := by
  rw [b.interior_convexHull]
  intro j
  exact b.coord_pos_of_mem_intrinsicInterior_convexHull_image
    (s := univ) (by simpa using hx) (mem_univ j)

end AffineBasis
