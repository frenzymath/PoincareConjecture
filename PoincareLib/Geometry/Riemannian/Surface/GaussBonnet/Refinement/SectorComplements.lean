import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.RestrictionAncestry

/-!
# Closed complementary sectors

The complement of the interior exchanges a convex affine sector with its
closed reflex sector. These set identities preserve the boundary rays used
by the actual core and collar supports.
-/

set_option autoImplicit false
open Set
open Poincare.Topology.Plane.Meshes

namespace PoincareMT.Topology.Surface

theorem interior_affine_halfspace_nonneg (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) :
    interior {z | 0 ≤ l z} = {z | 0 < l z} := by
  change interior (l ⁻¹' Ici (0 : ℝ)) = l ⁻¹' Ioi (0 : ℝ)
  rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
    l.continuous_of_finiteDimensional, interior_Ici]

theorem interior_affine_halfspace_nonpos (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) :
    interior {z | l z ≤ 0} = {z | l z < 0} := by
  change interior (l ⁻¹' Iic (0 : ℝ)) = l ⁻¹' Iio (0 : ℝ)
  rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
    l.continuous_of_finiteDimensional, interior_Iic]

/-- The affine sector interior is defined by both strict inequalities. -/
theorem interior_convexSector (c : AffineBasis (Fin 3) ℝ Plane) :
    interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} =
      {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z} := by
  have hs (i : Fin 3) (hi : i ≠ 0) : Function.Surjective (c.coord i) := by
    intro r
    exact ⟨AffineMap.lineMap (c 0) (c i) r, by
      simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hi]⟩
  change interior ({z | 0 ≤ c.coord 1 z} ∩ {z | 0 ≤ c.coord 2 z}) = _
  rw [interior_inter, interior_affine_halfspace_nonneg _ (hs 1 (by decide)),
    interior_affine_halfspace_nonneg _ (hs 2 (by decide))]
  rfl

/-- A convex collar sector leaves the closed reflex core sector. -/
theorem compl_interior_convexSector (c : AffineBasis (Fin 3) ℝ Plane) :
    (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ =
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  rw [interior_convexSector]
  ext z
  simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt]

/-- A reflex collar sector leaves precisely the closed convex core sector. -/
theorem compl_interior_reflexSector (c : AffineBasis (Fin 3) ℝ Plane) :
    (interior {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0})ᶜ =
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  rw [← compl_interior_convexSector, interior_compl, compl_compl,
    closure_interior_convexSector]

end PoincareMT.Topology.Surface
