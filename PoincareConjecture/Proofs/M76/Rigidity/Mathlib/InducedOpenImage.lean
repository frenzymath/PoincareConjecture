import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

open Set

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

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
