import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]



theorem subset_interior_or_compl_of_disjoint_frontier
    {K V : Set X} (hK : IsClosed K) (hV : IsPreconnected V)
    (havoid : Disjoint V (frontier K)) : V ⊆ interior K ∨ V ⊆ Kᶜ := by
  apply IsPreconnected.subset_or_subset isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) _ hV
  intro x hx
  by_cases hxK : x ∈ K
  · left
    by_contra hnot
    exact Set.disjoint_left.mp havoid hx
      ((mem_frontier_iff_notMem_interior hxK).mpr hnot)
  · exact Or.inr hxK




theorem opposite_sides_of_frontier_cover [PreconnectedSpace X]
    {K U V W : Set X} (hK : IsClosed K) (hU : IsOpen U)
    (hinterior : (interior K).Nonempty) (hproper : K ≠ univ)
    (hboundary : frontier K ⊆ U) (hcover : U ⊆ V ∪ frontier K ∪ W)
    (hV : IsPreconnected V) (hW : IsPreconnected W)
    (hVB : Disjoint V (frontier K)) (hWB : Disjoint W (frontier K)) :
    (V ⊆ interior K ∧ W ⊆ Kᶜ) ∨ (V ⊆ Kᶜ ∧ W ⊆ interior K) := by
  have hfrontier : (frontier K).Nonempty := nonempty_frontier_iff.mpr
    ⟨hinterior.mono interior_subset, hproper⟩
  have hbothInside (hVK : V ⊆ interior K) (hWK : W ⊆ interior K) : False := by
    have hUK : U ⊆ K := by
      intro x hx
      rcases hcover hx with (hx | hx) | hx
      · exact interior_subset (hVK hx)
      · exact hK.frontier_subset hx
      · exact interior_subset (hWK hx)
    obtain ⟨x, hx⟩ := hfrontier
    exact hx.2 (interior_maximal hUK hU (hboundary hx))
  have hbothOutside (hVK : V ⊆ Kᶜ) (hWK : W ⊆ Kᶜ) : False := by
    have hdisjoint : Disjoint U (interior K) := by
      apply Set.disjoint_left.mpr
      intro x hx hxK
      rcases hcover hx with (hx | hx) | hx
      · exact hVK hx (interior_subset hxK)
      · exact hx.2 hxK
      · exact hWK hx (interior_subset hxK)
    have hinteriorProper : interior K ≠ univ := by
      intro h
      exact hproper (eq_univ_of_univ_subset (h ▸ interior_subset))
    obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨hinterior, hinteriorProper⟩
    exact Set.disjoint_left.mp (hdisjoint.closure_right hU)
      (hboundary (frontier_interior_subset hx)) (frontier_subset_closure hx)
  rcases subset_interior_or_compl_of_disjoint_frontier hK hV hVB with hVK | hVK
  · rcases subset_interior_or_compl_of_disjoint_frontier hK hW hWB with hWK | hWK
    · exact (hbothInside hVK hWK).elim
    · exact Or.inl ⟨hVK, hWK⟩
  · rcases subset_interior_or_compl_of_disjoint_frontier hK hW hWB with hWK | hWK
    · exact Or.inr ⟨hVK, hWK⟩
    · exact (hbothOutside hVK hWK).elim

end Poincare.Topology
