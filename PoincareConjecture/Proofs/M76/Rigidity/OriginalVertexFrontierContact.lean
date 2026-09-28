import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBaseSets

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem nonboundary_base_contact_empty {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hsF : s ∉ (T.marked 1).faces) :
    T.diskDualBase s ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  have hnot : s ∉ (T.marked 3).faces := fun h => hsF (T.rim_le_boundary h)
  change (T.dualRegion s ∩ (T.marked 2).space) ∩ (T.marked 1).space = ∅
  rw [T.dualRegion_inter_disk, T.disk_dual_inter_boundary]
  exact (T.marked 3).barycentricDualBlock_space_eq_empty_of_not_face
    ((T.marked 2).nonempty_of_mem_faces hs) hnot

open Classical in

theorem vertex_mem_boundary_of_dual_contact (p : (T.marked 2).vertices)
    {x : T.index → ℝ × V3} (hxN : x ∈ (T.vertexBlock p).space)
    (hxF : x ∈ (T.marked 1).space) : (p : T.index → ℝ × V3) ∈ (T.marked 1).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  by_contra hn
  have hnot : {(p : T.index → ℝ × V3)} ∉ (T.marked 1).faces :=
    fun h => hn ((T.marked 1).vertices_subset_space h)
  have he : (T.vertexBlock p).space ∩ (T.marked 1).space = ∅ := by
    rw [show (T.vertexBlock p).space =
      (T.ambient.barycentricDualBlock {(p : T.index → ℝ × V3)}).space from rfl,
      T.ambient.barycentricDualBlock_space_inter_subcomplex
        (T.marked 1) (T.marked_le 1)]
    exact (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.singleton_nonempty _) hnot
  exact he.subset ⟨hxN, hxF⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
