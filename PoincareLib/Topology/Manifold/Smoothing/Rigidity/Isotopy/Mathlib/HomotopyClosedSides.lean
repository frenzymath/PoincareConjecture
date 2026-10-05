import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Basic

/-!
# Whole closed sides preserved by an exact frontier preimage

A continuous time path that avoids a frontier cannot change closed-side
membership. Points on that frontier stay in the closed side. This proves
the full side, interior and closed-exterior preimage identities needed
before compression of the original transverse levels. See Waldhausen1968,
pp.58--60, and rigidity057, section1.
-/

set_option autoImplicit false

open Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Exact full frontier preimages throughout a continuous homotopy
preserve the entire preimage of a closed set. No side or real-lift
condition is assumed. See rigidity057, section1. -/
theorem preimage_eq_of_frontier_preimage_eq
    (H : C(unitInterval × X, Y)) {A : Set Y} (hA : IsClosed A)
    (hfront : ∀ t : unitInterval,
      (fun x => H (t, x)) ⁻¹' frontier A = (fun x => H (0, x)) ⁻¹' frontier A)
    (t : unitInterval) :
    (fun x => H (t, x)) ⁻¹' A = (fun x => H (0, x)) ⁻¹' A := by
  ext x
  by_cases hx : H (0, x) ∈ frontier A
  · have hxt : H (t, x) ∈ frontier A := by
      change x ∈ (fun y => H (t, y)) ⁻¹' frontier A
      rw [hfront t]
      exact hx
    exact iff_of_true (hA.frontier_subset hxt) (hA.frontier_subset hx)
  · let h : C(unitInterval, Y) :=
      ⟨fun u => H (u, x), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hboundary : frontier (h ⁻¹' A) = ∅ := by
      apply subset_empty_iff.mp
      intro u hu
      have huA : H (u, x) ∈ frontier A := h.continuous.frontier_preimage_subset A hu
      have huA' : x ∈ (fun y => H (u, y)) ⁻¹' frontier A := huA
      rw [hfront u] at huA'
      exact hx huA'
    have hcl : IsClopen (h ⁻¹' A) := isClopen_iff_frontier_eq_empty.mpr hboundary
    change t ∈ h ⁻¹' A ↔ (0 : unitInterval) ∈ h ⁻¹' A
    rcases isClopen_iff.mp hcl with he | he
    · simp only [he, mem_empty_iff_false]
    · simp only [he, mem_univ]

/-- The same exact frontier condition also preserves the entire
interior and closed-exterior preimages. This uses the set difference
formula for interior, not commutation of interior with arbitrary
continuous preimages. See rigidity057, section1. -/
theorem side_preimages_eq_of_frontier_preimage_eq
    (H : C(unitInterval × X, Y)) {A : Set Y} (hA : IsClosed A)
    (hfront : ∀ t : unitInterval,
      (fun x => H (t, x)) ⁻¹' frontier A = (fun x => H (0, x)) ⁻¹' frontier A)
    (t : unitInterval) :
    (fun x => H (t, x)) ⁻¹' A = (fun x => H (0, x)) ⁻¹' A ∧
      (fun x => H (t, x)) ⁻¹' interior A = (fun x => H (0, x)) ⁻¹' interior A ∧
      (fun x => H (t, x)) ⁻¹' (interior A)ᶜ =
        (fun x => H (0, x)) ⁻¹' (interior A)ᶜ := by
  have hclosed := H.preimage_eq_of_frontier_preimage_eq hA hfront t
  have hinterior : (fun x => H (t, x)) ⁻¹' interior A =
      (fun x => H (0, x)) ⁻¹' interior A := by
    rw [← self_sdiff_frontier A, preimage_sdiff, preimage_sdiff, hclosed, hfront t]
  exact ⟨hclosed, hinterior, by rw [preimage_compl, preimage_compl, hinterior]⟩

end ContinuousMap
