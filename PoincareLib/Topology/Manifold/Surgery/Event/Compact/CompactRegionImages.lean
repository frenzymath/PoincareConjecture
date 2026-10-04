import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

/-!
# Exact frontiers under coordinates containing a compact closure

A chart containing the whole compact closure cannot introduce a new
frontier at the edge of its target. These identities transport the actual
event component's finite boundary, rather than a containing canonical set.
-/

set_option autoImplicit false

open Set Topology

namespace PoincareMT.M38

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- A partial homeomorphism defined on a compact closure carries that
closure onto the closure of the image. -/
theorem partialHomeomorph_image_closure (e : OpenPartialHomeomorph X Y)
    {U : Set X} (hcompact : IsCompact (closure U)) (hsource : closure U ⊆ e.source) :
    e '' closure U = closure (e '' U) := by
  apply Subset.antisymm
  · exact (e.continuousOn.mono hsource).image_closure
  · exact closure_minimal (image_mono subset_closure)
      (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed

/-- The frontier is transported exactly, including when the original
region is a proper subset of the chart source. -/
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

end PoincareMT.M38
