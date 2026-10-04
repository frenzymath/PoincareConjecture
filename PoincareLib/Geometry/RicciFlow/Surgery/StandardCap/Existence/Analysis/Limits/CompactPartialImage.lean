import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact closures and frontiers under actual partial homeomorphisms

Compact capture inside the source makes the local closure and frontier
identities global on the displayed image. Source: Morgan-Tian
Proposition 9.79, p. 234; cap-ball-confinement.md.
-/

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y) {S : Set X}

namespace StandardCapImport

/-- The literal image of a subset of the actual source satisfies the
local image relation (cap transport, Proposition 9.79). -/
theorem isImage_image_of_subset_source (hS : S ⊆ e.source) : e.IsImage S (e '' S) := by
  intro x hx
  constructor
  · rintro ⟨y, hy, he⟩
    exact e.injOn (hS hy) hx he ▸ hy
  · exact mem_image_of_mem e

end StandardCapImport

export StandardCapImport (isImage_image_of_subset_source)

/-- A compact source closure has exactly its actual image closure;
continuity is needed only on the partial map's displayed source
(cap transport, Proposition 9.79). -/
theorem image_closure_eq_of_isCompact [T2Space Y]
    (hK : IsCompact (closure S)) (hsource : closure S ⊆ e.source) :
    e '' closure S = closure (e '' S) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ((e.continuousOn x (hsource hx)).mono (subset_closure.trans hsource)).mem_closure_image hx
  · apply closure_minimal (image_mono subset_closure)
    exact (hK.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed

/-- Compact capture puts every actual image-closure point in the open
target of the partial map (cap transport, Proposition 9.79). -/
theorem closure_image_subset_target_of_isCompact [T2Space Y]
    (hK : IsCompact (closure S)) (hsource : closure S ⊆ e.source) :
    closure (e '' S) ⊆ e.target := by
  rw [← e.image_closure_eq_of_isCompact hK hsource]
  rintro _ ⟨x, hx, rfl⟩
  exact e.map_source (hsource hx)

/-- The full actual frontier is transported whenever the compact
closure is captured in the source, with no openness assumption on S
(cap transport, Proposition 9.79). -/
theorem image_frontier_eq_of_isCompact [T2Space Y]
    (hK : IsCompact (closure S)) (hsource : closure S ⊆ e.source) :
    e '' frontier S = frontier (e '' S) := by
  have himage := e.isImage_image_of_subset_source (subset_closure.trans hsource)
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (himage.frontier.apply_mem_iff (hsource (frontier_subset_closure hx))).mpr hx
  · intro y hy
    have htarget := e.closure_image_subset_target_of_isCompact hK hsource
      (frontier_subset_closure hy)
    exact ⟨e.symm y, (himage.frontier.symm_apply_mem_iff htarget).mpr hy,
      e.right_inv htarget⟩

end OpenPartialHomeomorph
