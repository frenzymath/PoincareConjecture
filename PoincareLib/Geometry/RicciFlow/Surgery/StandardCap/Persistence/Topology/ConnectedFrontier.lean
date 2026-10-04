import Mathlib.Topology.Connected.Basic

/-!
# Connected sets avoiding a frontier

The final connectedness step in Morgan--Tian, Claim 16.10, p. 375:
a connected tracked region cannot meet both sides of a surgery frontier
without meeting that frontier.
-/

set_option autoImplicit false

open Set

/-- A preconnected set avoiding a frontier lies on one side of it.
This is the topological step in Morgan--Tian, Claim 16.10, p. 375. -/
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

/-- If one point of a preconnected region avoiding a frontier is lost,
the whole region is outside the retained interior (Claim 16.10, p. 375). -/
theorem IsPreconnected.subset_compl_interior_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsPreconnected U) (hboundary : Disjoint U (frontier V))
    (hlost : ∃ x ∈ U, x ∉ interior V) : U ⊆ (interior V)ᶜ := by
  obtain hin | hout := hU.subset_interior_or_compl_closure hboundary
  · obtain ⟨x, hx, hnot⟩ := hlost
    exact (hnot (hin hx)).elim
  · exact hout.trans (compl_subset_compl.mpr (interior_subset.trans subset_closure))
