import PoincareConjecture.Proofs.M34.Mathlib.CompactPartialImage
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {D : Set X}

theorem image_frontier_eq_target_inter_of_closure_subset (hD : closure D ⊆ e.source) :
    e '' frontier D = e.target ∩ frontier (e '' D) := by
  have hh := (e.isImage_image_of_subset_source (subset_closure.trans hD)).frontier.image_eq
  rwa [inter_eq_right.mpr (frontier_subset_closure.trans hD)] at hh

theorem image_region_of_isCompact_closure [T2Space Y] (hD : IsOpen D)
    (hcompact : IsCompact (closure D)) (hsource : closure D ⊆ e.source) :
    IsOpen (e '' D) ∧ IsCompact (closure (e '' D)) ∧
      closure (e '' D) = e '' closure D ∧ frontier (e '' D) = e '' frontier D := by
  have hs : D ⊆ e.source := subset_closure.trans hsource
  have hi := e.isImage_image_of_subset_source hs
  have hc := hcompact.image_of_continuousOn (e.continuousOn.mono hsource)
  have hct : closure (e '' D) ⊆ e.target := by
    apply Subset.trans (b := e '' closure D) _
      (image_subset_iff.mpr fun _ hz => e.map_source (hsource hz))
    exact closure_minimal (image_mono subset_closure) hc.isClosed
  have hcl : closure (e '' D) = e '' closure D := by
    have hh := hi.closure.image_eq
    rw [inter_eq_right.mpr hsource, inter_eq_right.mpr hct] at hh
    exact hh.symm
  have hfront : frontier (e '' D) = e '' frontier D := by
    have hh := hi.frontier.image_eq
    rw [inter_eq_right.mpr (frontier_subset_closure.trans hsource),
      inter_eq_right.mpr (frontier_subset_closure.trans hct)] at hh
    exact hh.symm
  exact ⟨e.isOpen_image_of_subset_source hD hs, hcl.symm ▸ hc, hcl, hfront⟩

end OpenPartialHomeomorph
