import Mathlib.Topology.Connected.Basic










set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane



theorem preconnected_local_sides_subset_regions {X : Type*} [TopologicalSpace X]
    {I O C W A B : Set X} {q : X}
    (hI : IsOpen I) (hO : IsOpen O) (hIO : Disjoint I O) (hcover : I ∪ O = Cᶜ)
    (hW : IsOpen W) (hqW : q ∈ W) (hq : q ∈ frontier I)
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hlocal : A ∪ B = W \ C)
    (hBO : (B ∩ O).Nonempty) : A ⊆ I ∧ B ⊆ O := by
  have hAC : A ⊆ I ∪ O := by
    intro x hx
    rw [hcover]
    exact (show x ∈ W \ C from hlocal ▸ Or.inl hx).2
  have hBC : B ⊆ I ∪ O := by
    intro x hx
    rw [hcover]
    exact (show x ∈ W \ C from hlocal ▸ Or.inr hx).2
  have hBO' : B ⊆ O := hB.subset_right_of_subset_union hI hO hIO hBC hBO
  obtain ⟨x, hxW, hxI⟩ := mem_closure_iff.mp (frontier_subset_closure hq) W hW hqW
  have hxC : x ∈ Cᶜ := hcover ▸ Or.inl hxI
  have hxAB : x ∈ A ∪ B := hlocal.symm ▸ (show x ∈ W \ C from ⟨hxW, hxC⟩)
  have hxA : x ∈ A := hxAB.resolve_right fun hxB => Set.disjoint_left.mp hIO hxI (hBO' hxB)
  exact ⟨hA.subset_left_of_subset_union hI hO hIO hAC ⟨x, hxA, hxI⟩, hBO'⟩

end Poincare.Manifold.Schoenflies.Plane
