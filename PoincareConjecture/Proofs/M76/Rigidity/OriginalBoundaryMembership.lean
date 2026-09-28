import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskModelFacts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem frontier_subset_neighborhood : frontier R ⊆ T.neighborhood :=
  frontier_subset_closure.trans (closure_minimal
    (T.region_interior.trans interior_subset) T.compact_neighborhood.isClosed)

theorem inverse_mem_boundary_iff {x : T.index → ℝ × V3}
    (hx : x ∈ T.ambient.space) :
    (T.inverse x : X) ∈ frontier R ↔ x ∈ (T.marked 1).space := by
  rw [T.boundary_space]
  exact original_model_mem_image_iff T.model T.graph T.inverse T.model_eq T.inverse_eq
    T.frontier_subset_neighborhood ⟨x, hx⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
