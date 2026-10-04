import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.Relative.Regions.Duals
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricNeighborhoodCarrier

/-! # Neighborhoods in the complete proper surface product

The finite derived neighborhood contains the whole marked surface.
Pulling it back through the actual finite model retains both the original
relative neighborhood and the inverse equation on that neighborhood.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (T : CoorientedSurfaceStars E)

/-- The complete union of surface-vertex dual regions contains a relative
neighborhood of the entire surface in the region. -/
theorem exists_open_neighborhood_in_dual_union :
    ∃ U : Set E, IsOpen U ∧ (T.marked 2).space ⊆ U ∧
      U ∩ (T.marked 0).space ⊆
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  obtain ⟨U, hU, hSU, hUN⟩ :=
    T.ambient.exists_open_barycentricNeighborhood (T.marked_le 2)
  refine ⟨U, hU, hSU, ?_⟩
  rintro x ⟨hxU, hxR⟩
  have hxN := hUN ⟨hxU, space_subset_of_le (T.marked_le 0) hxR⟩
  rw [T.ambient.barycentricNeighborhood_space_eq_iUnion_dualBlocks] at hxN
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxN
  exact mem_iUnion.mpr ⟨⟨p, hp⟩, ⟨hxp, hxR⟩⟩

/-- Transport the finite derived neighborhood through an actual model.
The ambient open neighborhood stays inside the model domain, and every
point of its intersection with the region has its original inverse. -/
theorem exists_realized_neighborhood_in_dual_union
    {X : Type*} [TopologicalSpace X] {C W S : Set X}
    {F : X → E} (hF : Continuous F)
    (H : C ≃ₜ T.ambient.space) (g : E → C)
    (hW : W ⊆ interior C) (hS : S ⊆ W)
    (hregion : (T.marked 0).space = F '' W)
    (hsurface : (T.marked 2).space = F '' S)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : T.ambient.space, (g z : X) = (H.symm z : X)) :
    ∃ O : Set X, IsOpen O ∧ S ⊆ O ∧ O ⊆ interior C ∧
      O ∩ W ⊆ (fun z => (g z : X)) ''
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}) ∧
      ∀ x ∈ O ∩ W,
        F x ∈ (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}) ∧
        (g (F x) : X) = x := by
  obtain ⟨U, hU, hSU, hUN⟩ := T.exists_open_neighborhood_in_dual_union
  let O : Set X := F ⁻¹' U ∩ interior C
  have hlocal : ∀ x ∈ O ∩ W,
      F x ∈ (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : E)}) ∧
      (g (F x) : X) = x := by
    rintro x ⟨hxO, hxW⟩
    have hxC : x ∈ C := interior_subset hxO.2
    refine ⟨hUN ⟨hxO.1, hregion.symm.subset ⟨x, hxW, rfl⟩⟩, ?_⟩
    rw [← hH ⟨x, hxC⟩, hg (H ⟨x, hxC⟩), H.symm_apply_apply]
  refine ⟨O, (hU.preimage hF).inter isOpen_interior, ?_,
    inter_subset_right, ?_, hlocal⟩
  · intro x hxS
    exact ⟨hSU (hsurface.symm.subset ⟨x, hxS, rfl⟩), hW (hS hxS)⟩
  · intro x hx
    exact ⟨F x, (hlocal x hx).1, (hlocal x hx).2⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars
