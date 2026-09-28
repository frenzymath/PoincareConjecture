import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeSides








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension G T} {K : TerminalComponentPath E} (e : TerminalEnd K)

theorem exists_cappedTube_direction
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (Y : CappedTubeCertificate (E.extended.metric T)) (n : ℕ)
    (htail : Subtype.val '' e.tail n ⊆ Y.carrier) :
    ∀ a ∈ Ioo (0 : ℝ) 1, ∃ k : ℕ, n ≤ k ∧
      ∀ m : ℕ, k ≤ m →
        Subtype.val '' e.tail m ⊆ Y.tube.cylinder.tail (!Y.attachment_side) a := by
  obtain ⟨k, hk⟩ := e.exists_tail_disjoint_cap hproper Y.cap
  let m := max n k
  have hsub : Subtype.val '' e.tail m ⊆ Y.tube.carrier := by
    intro x hx
    have hxY := htail (image_mono (e.nested (le_max_left _ _)) hx)
    rw [Y.carrier_eq_union] at hxY
    exact hxY.resolve_left (fun h => disjoint_left.mp (hk m (le_max_right _ _)) hx h)
  let tube : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail m) :=
    { Y.tube with contains_X := hsub }
  obtain ⟨side, hside⟩ := e.exists_tube_direction m tube
  have hne : side ≠ Y.attachment_side := by
    intro heq
    obtain ⟨a, ha, hcap⟩ := Y.attachment.tube_tail
    obtain ⟨l, _, hl⟩ := hside a ha
    apply e.tail_image_not_subset_compact l
      (Y.cap.isCompact_closure_of_scalar_proper (E.extended.connection T) hproper)
    apply (hl l le_rfl).trans
    exact (show tube.cylinder.tail side a ⊆ Y.cap.carrier by
      simpa only [tube, heq] using hcap).trans subset_closure
  have heq : side = !Y.attachment_side := by
    cases side <;> cases h : Y.attachment_side <;> simp_all
  intro a ha
  obtain ⟨l, hml, hl⟩ := hside a ha
  refine ⟨l, (le_max_left n k).trans hml, ?_⟩
  simpa only [tube, heq] using hl

end PoincareConjecture.TerminalEnd
