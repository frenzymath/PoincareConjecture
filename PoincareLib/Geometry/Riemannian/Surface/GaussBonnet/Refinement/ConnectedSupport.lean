import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Regular

/-!
# Recovering support membership away from a frontier

A connected sector avoiding a closed support's frontier is wholly inside
or wholly outside that support. This transfers a geometric test point to
the entire open sector when reconstructing cap-union support germs.
-/

set_option autoImplicit false
open Set

namespace PoincareMT.Topology.Surface

/-- A connected region disjoint from a closed set's frontier is either
inside its interior or outside the entire closed set. -/
theorem preconnected_subset_interior_or_compl_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {U K : Set X}
    (hU : IsPreconnected U) (hK : IsClosed K) (hfront : Disjoint U (frontier K)) :
    U ⊆ interior K ∨ U ⊆ Kᶜ := by
  apply hU.subset_or_subset isOpen_interior hK.isOpen_compl
  · exact disjoint_left.mpr fun _ hi hn => hn (interior_subset hi)
  · intro x hx
    by_cases hmem : x ∈ K
    · left
      by_contra hn
      exact disjoint_left.mp hfront hx ⟨subset_closure hmem, hn⟩
    · exact Or.inr hmem

/-- Support membership is constant on a connected region avoiding the
frontier, so an actual point determines the occupied side. -/
theorem mem_closed_iff_of_preconnected_avoiding_frontier
    {X : Type*} [TopologicalSpace X] {U K : Set X}
    (hU : IsPreconnected U) (hK : IsClosed K) (hfront : Disjoint U (frontier K))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : x ∈ K ↔ y ∈ K := by
  rcases preconnected_subset_interior_or_compl_of_disjoint_frontier hU hK hfront with hi | ho
  · exact iff_of_true (interior_subset (hi hx)) (interior_subset (hi hy))
  · exact iff_of_false (ho hx) (ho hy)

end PoincareMT.Topology.Surface
