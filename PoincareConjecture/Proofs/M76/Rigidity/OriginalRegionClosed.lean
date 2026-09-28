import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryMembership
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskParameter









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)



theorem inverse_region_image :
    (fun x => (T.inverse x : X)) '' (T.marked 0).space = R := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (T.inverse_mem_region_iff
      (SimplicialComplex.space_subset_of_le (T.marked_le 0) hx)).mpr hx
  · intro y hy
    have hyC : y ∈ T.neighborhood := interior_subset (T.region_interior hy)
    have hFy : T.graph y ∈ (T.marked 0).space :=
      T.region_space.symm.subset ⟨y, hy, rfl⟩
    refine ⟨T.graph y, hFy, ?_⟩
    change (T.inverse (T.graph y) : X) = y
    rw [← T.model_eq ⟨y, hyC⟩, T.inverse_eq (T.model ⟨y, hyC⟩),
      T.model.symm_apply_apply]

include T in


theorem isCompact_region : IsCompact R := by
  rw [← T.inverse_region_image]
  exact ((T.marked 0).isCompact_space_of_finite (T.marked_finite 0)).image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn
      (T.inverse_continuous.mono (SimplicialComplex.space_subset_of_le (T.marked_le 0))))

variable [T2Space X]

include T in


theorem isClosed_region : IsClosed R := T.isCompact_region.isClosed



theorem boundary_space_subset_region : (T.marked 1).space ⊆ (T.marked 0).space := by
  rw [T.boundary_space, T.region_space]
  exact image_mono T.isClosed_region.frontier_subset

end PoincareConjecture.M76.OriginalProperDiskTriangulation
