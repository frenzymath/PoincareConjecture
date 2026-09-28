import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBlocks

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem vertex_base_eq_inter (p : (T.marked 2).vertices) :
    T.diskDualBase {(p : T.index → ℝ × V3)} =
      (T.vertexBlock p).space ∩ (T.marked 2).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  change ((T.vertexBlock p).space ∩ (T.marked 0).space) ∩
    (T.marked 2).space = (T.vertexBlock p).space ∩ (T.marked 2).space
  exact Set.ext (fun _ => ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, T.disk_space_subset_region h.2⟩, h.2⟩⟩)

open Classical in

theorem vertex_base_rim_eq (p : (T.marked 2).vertices) :
    T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space =
      (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ ((T.vertexBlock p).link p).space) ∪
        (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hlink : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (show N.link p ≤ N from fun _ hs => hs.1)
  have hrim : T.dualRegionRim {(p : T.index → ℝ × V3)} =
      ((N.link p).space ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space) := by
    dsimp only [dualRegionRim]
    rw [Finset.centroid_singleton]
    rfl
  rw [hrim, T.vertex_base_eq_inter]
  change (((N.link p).space ∩ (T.marked 0).space) ∪
      (N.space ∩ (T.marked 1).space)) ∩ (T.marked 2).space =
    ((N.space ∩ (T.marked 2).space) ∩ (N.link p).space) ∪
      ((N.space ∩ (T.marked 2).space) ∩ (T.marked 1).space)
  ext x
  constructor
  · rintro ⟨hx | hx, hxD⟩
    · exact Or.inl ⟨⟨hlink hx.1, hxD⟩, hx.1⟩
    · exact Or.inr ⟨⟨hx.1, hxD⟩, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨Or.inl ⟨hx.2, T.disk_space_subset_region hx.1.2⟩, hx.1.2⟩
    · exact ⟨Or.inr ⟨hx.1.1, hx.2⟩, hx.1.2⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
