import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set

theorem IsPreconnected.subset_interior_or_compl_closure
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsPreconnected U) (hboundary : Disjoint U (frontier V)) :
    U ⊆ interior V ∨ U ⊆ (closure V)ᶜ := by
  apply hU.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
  · exact disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  · intro x hx
    by_cases hin : x ∈ interior V
    · exact Or.inl hin
    · right
      intro hclosure
      exact Set.disjoint_left.mp hboundary hx ⟨hclosure, hin⟩

theorem IsPreconnected.subset_compl_interior_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsPreconnected U) (hboundary : Disjoint U (frontier V))
    (hlost : ∃ x ∈ U, x ∉ interior V) : U ⊆ (interior V)ᶜ := by
  obtain hin | hout := hU.subset_interior_or_compl_closure hboundary
  · obtain ⟨x, hx, hnot⟩ := hlost
    exact (hnot (hin hx)).elim
  · exact hout.trans (compl_subset_compl.mpr (interior_subset.trans subset_closure))
