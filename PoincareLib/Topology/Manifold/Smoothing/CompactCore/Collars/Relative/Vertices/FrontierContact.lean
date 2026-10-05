import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.Relative.Vertices.Blocks
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.Relative.Model.SurfaceIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "I" => Icc (-1 : ℝ) 1

/-- A nonboundary disk face has no whole-base old-frontier contact.
The actual rim dual is empty because its label is not a rim face.
See rigidity031, section2. -/
theorem nonboundary_base_contact_empty {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsF : s ∉ (T.marked 1).faces) :
    T.surfaceBase s ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  have hnot : s ∉ (T.marked 3).faces := fun h => hsF (T.rim_le_boundary h)
  change (T.dualRegion s ∩ (T.marked 2).space) ∩ (T.marked 1).space = ∅
  rw [T.dualRegion_inter_surface, T.surface_dual_inter_boundary]
  exact (T.marked 3).barycentricDualBlock_space_eq_empty_of_not_face
    ((T.marked 2).nonempty_of_mem_faces hs) hnot

open Classical in
/-- Contact of any point of the whole vertex dual with the actual
old-boundary mark forces its original vertex into that mark.
See rigidity031, section2. -/
theorem vertex_mem_boundary_of_dual_contact (p : (T.marked 2).vertices)
    {x : E} (hxN : x ∈ (T.vertexBlock p).space)
    (hxF : x ∈ (T.marked 1).space) : (p : E) ∈ (T.marked 1).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  by_contra hn
  have hnot : {(p : E)} ∉ (T.marked 1).faces :=
    fun h => hn ((T.marked 1).vertices_subset_space h)
  have he : (T.vertexBlock p).space ∩ (T.marked 1).space = ∅ := by
    rw [show (T.vertexBlock p).space =
      (T.ambient.barycentricDualBlock {(p : E)}).space from rfl,
      T.ambient.barycentricDualBlock_space_inter_subcomplex
        (T.marked 1) (T.marked_le 1)]
    exact (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.singleton_nonempty _) hnot
  exact he.subset ⟨hxN, hxF⟩


end Geometry.SimplicialComplex.CoorientedSurfaceStars

