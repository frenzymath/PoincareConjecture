import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Regular









set_option autoImplicit false
open Set

namespace PoincareConjecture.Topology.Surface



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



theorem mem_closed_iff_of_preconnected_avoiding_frontier
    {X : Type*} [TopologicalSpace X] {U K : Set X}
    (hU : IsPreconnected U) (hK : IsClosed K) (hfront : Disjoint U (frontier K))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : x ∈ K ↔ y ∈ K := by
  rcases preconnected_subset_interior_or_compl_of_disjoint_frontier hU hK hfront with hi | ho
  · exact iff_of_true (interior_subset (hi hx)) (interior_subset (hi hy))
  · exact iff_of_false (ho hx) (ho hy)

end PoincareConjecture.Topology.Surface
