import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff









set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]



theorem partialHomeomorph_image_closure (e : OpenPartialHomeomorph X Y)
    {U : Set X} (hcompact : IsCompact (closure U)) (hsource : closure U ⊆ e.source) :
    e '' closure U = closure (e '' U) := by
  apply Subset.antisymm
  · exact (e.continuousOn.mono hsource).image_closure
  · exact closure_minimal (image_mono subset_closure)
      (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed



theorem partialHomeomorph_image_frontier (e : OpenPartialHomeomorph X Y)
    {U : Set X} (hcompact : IsCompact (closure U)) (hsource : closure U ⊆ e.source) :
    e '' frontier U = frontier (e '' U) := by
  have himage : e.IsImage U (e '' U) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact e.injOn (hsource (subset_closure hy)) hx hyx ▸ hy
    · exact mem_image_of_mem _
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (himage.frontier (hsource (frontier_subset_closure hx))).mpr hx
  · intro y hy
    have hycl : y ∈ e '' closure U := by
      rw [partialHomeomorph_image_closure e hcompact hsource]
      exact frontier_subset_closure hy
    obtain ⟨x, hx, rfl⟩ := hycl
    exact ⟨x, (himage.frontier (hsource hx)).mp hy, rfl⟩

end PoincareConjecture.M38
