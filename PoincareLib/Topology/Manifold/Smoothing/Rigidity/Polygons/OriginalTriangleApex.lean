import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.OriginalRegionCofaces

/-!
# The actual opposite vertex of a disk-triangle coface

The full disk mark and its intrinsic face dimension exclude the
opposite tetrahedron vertex from the entire disk carrier.
See Hudson1969, pp.8--9 and rigidity019, section3.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

/-- The unique opposite vertex of an actual tetrahedral coface is
outside the complete original disk mark. See rigidity019, section3. -/
theorem exists_triangle_coface_apex
    {s t : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) (ht : t ∈ T.ambient.faces) (htcard : t.card = 4)
    (hst : s ⊆ t) :
    ∃ v, v ∉ s ∧ insert v s = t ∧ v ∉ (T.marked 2).space := by
  classical
  obtain ⟨v, hvs, hvt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hst, (show s.card + 1 = t.card by omega)⟩
  refine ⟨v, hvs, hvt, ?_⟩
  intro hvD
  have hvt' : v ∈ t := hvt ▸ Finset.mem_insert_self v s
  have hvK := T.ambient.face_subset_vertices ht hvt'
  have hv : v ∈ (T.marked 2).vertices :=
    (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 2) hvK).mp hvD
  have htD : t ∈ (T.marked 2).faces := by
    apply T.marked_full 2 t ht
    intro z hz
    rw [← hvt] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzs
    · exact hv
    · exact (T.marked 2).face_subset_vertices hs hzs
  have hbound := T.disk_face_card_le htD
  omega

end PoincareMT.M76.OriginalProperDiskTriangulation
