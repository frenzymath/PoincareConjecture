import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.TwoRaySupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace PoincareConjecture.Topology.Surface

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem preimage_regular_closed_germ
    (F : OpenPartialHomeomorph X Y) (A : Set Y)
    (hregular : closure (interior A) = A) {q : X} (hq : q ∈ F.source) :
    closure (interior (F ⁻¹' A)) =ᶠ[𝓝 q] F ⁻¹' A := by
  have hi : interior (F ⁻¹' A) =ᶠ[𝓝 q] F ⁻¹' interior A := by
    filter_upwards [F.open_source.mem_nhds hq] with z hz
    have h := congrArg (fun K : Set X => z ∈ K) (F.preimage_interior A)
    change (z ∈ interior (F ⁻¹' A)) = (F z ∈ interior A)
    simpa only [mem_inter_iff, hz, true_and, mem_preimage] using h.symm
  have hc := support_eventuallyEq_closure hi
  filter_upwards [hc, F.open_source.mem_nhds hq] with z hz hzs
  have h := congrArg (fun K : Set X => z ∈ K) (F.preimage_closure (interior A))
  simp only [mem_inter_iff, hzs, true_and, mem_preimage, hregular] at h
  exact hz.trans h.symm

theorem regular_closed_complement_interior_germ
    {A K : Set X} {q : X}
    (hregular : closure (interior A) =ᶠ[𝓝 q] A)
    (hK : K =ᶠ[𝓝 q] (interior A)ᶜ) : A =ᶠ[𝓝 q] (interior K)ᶜ := by
  have hi := support_eventuallyEq_interior hK
  rw [interior_compl] at hi
  filter_upwards [hregular, hi] with z hr hz
  apply propext
  change z ∈ A ↔ ¬z ∈ interior K
  have h : z ∈ interior K ↔ ¬z ∈ closure (interior A) := propext_iff.mp hz
  rw [h, not_not]
  exact (propext_iff.mp hr).symm

end PoincareConjecture.Topology.Surface
