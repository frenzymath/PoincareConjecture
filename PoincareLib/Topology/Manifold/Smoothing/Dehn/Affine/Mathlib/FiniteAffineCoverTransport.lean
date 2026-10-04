import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Transport finite affine dimension covers through actual PL maps

Use the finitely many actual affine formulas of the map on its
stated carrier. The image of each covering affine subspace under
each formula has no larger direction dimension. The covered set
may be neither closed nor a polyhedron. See Dehn032, section7,
and Hudson1969, pp.15--19.
-/

set_option autoImplicit false

open Set

namespace Geometry

/-- A finite affine dimension cover transports through a finite
PL map by its actual finite affine formulas. This does not require
the covered subset itself to be closed, convex or polyhedral.
See Dehn032, section7. -/
theorem FinitePiecewiseAffineOn.exists_finite_affine_image_cover
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S C : Set E} (hf : FinitePiecewiseAffineOn f S) (hCS : C ⊆ S)
    (T : Finset (AffineSubspace ℝ E)) {d : ℕ}
    (hd : ∀ A ∈ T, Module.finrank ℝ A.direction ≤ d)
    (hcover : ∀ x ∈ C, ∃ A ∈ T, x ∈ A) :
    ∃ U : Finset (AffineSubspace ℝ F),
      (∀ B ∈ U, Module.finrank ℝ B.direction ≤ d) ∧
      ∀ y ∈ f '' C, ∃ B ∈ U, y ∈ B := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  let : Finite K.faces := hK.to_subtype
  choose a ha using fun s : K.faces => hfaces s.val s.property
  let cover (p : K.faces × T) : AffineSubspace ℝ F :=
    p.2.val.map (a p.1).toAffineMap
  let U := (finite_range cover).toFinset
  refine ⟨U, ?_, ?_⟩
  · intro B hB
    obtain ⟨p, rfl⟩ := (finite_range cover).mem_toFinset.mp hB
    change Module.finrank ℝ (p.2.val.map (a p.1).toAffineMap).direction ≤ d
    rw [AffineSubspace.map_direction]
    exact (Submodule.finrank_map_le _ _).trans (hd p.2.val p.2.property)
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (hCS hx)
    obtain ⟨A, hAT, hxA⟩ := hcover x hx
    let p : K.faces × T := (⟨s, hs⟩, ⟨A, hAT⟩)
    refine ⟨cover p, (finite_range cover).mem_toFinset.mpr ⟨p, rfl⟩, ?_⟩
    change f x ∈ A.map (a ⟨s, hs⟩).toAffineMap
    rw [ha ⟨s, hs⟩ hxs]
    exact mem_image_of_mem (a ⟨s, hs⟩).toAffineMap hxA

end Geometry
