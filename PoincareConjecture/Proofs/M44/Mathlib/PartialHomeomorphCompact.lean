import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem image_closure_of_compact_buffer (e : OpenPartialHomeomorph X Y)
    {V : Set X} (hV : IsCompact (closure V)) (hsub : closure V ⊆ e.source) :
    e '' closure V = closure (e '' V) := by
  have hc : ContinuousOn e (closure V) := e.continuousOn.mono hsub
  exact hc.image_closure.antisymm
    (closure_minimal (image_mono subset_closure) (hV.image_of_continuousOn hc).isClosed)

theorem image_frontier_of_compact_buffer (e : OpenPartialHomeomorph X Y)
    {V : Set X} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hsub : closure V ⊆ e.source) :
    e '' frontier V = frontier (e '' V) := by
  have hopen := e.isOpen_image_of_subset_source hV (subset_closure.trans hsub)
  rw [frontier, frontier, hV.interior_eq, hopen.interior_eq,
    ← e.image_closure_of_compact_buffer hcompact hsub]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_image_of_mem e hx.1, ?_⟩
    rintro ⟨y, hy, hxy⟩
    exact hx.2 (e.injOn (hsub (subset_closure hy)) (hsub hx.1) hxy ▸ hy)
  · rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    exact ⟨x, ⟨hx, fun hv => hnot (mem_image_of_mem e hv)⟩, rfl⟩

end OpenPartialHomeomorph
