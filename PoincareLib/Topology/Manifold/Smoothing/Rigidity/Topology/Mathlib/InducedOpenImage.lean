import Mathlib.Topology.Maps.Basic

/-!
# Open images inside an actual open part of an induced range

An open source subset has open ambient image when it is contained
in an ambient-open part of the range. This is the subspace-topology
step in rigidity035, section3.
-/

set_option autoImplicit false

open Set

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

/-- An actual open neighborhood inside the range promotes relative
openness of the complete image to ambient openness. See rigidity035. -/
theorem isOpen_image_of_subset_open (hf : IsInducing f)
    {S : Set X} (hS : IsOpen S) {W : Set Y} (hW : IsOpen W)
    (hSW : f '' S ⊆ W) (hWf : W ⊆ range f) : IsOpen (f '' S) := by
  obtain ⟨V, hV, hVS⟩ := hf.image_eq_isOpen_inter_range hS
  have heq : f '' S = V ∩ W := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(hVS.subset hy).1, hSW hy⟩
    · intro y hy
      exact hVS.symm.subset ⟨hy.1, hWf hy.2⟩
  rw [heq]
  exact hV.inter hW

end Topology.IsInducing
