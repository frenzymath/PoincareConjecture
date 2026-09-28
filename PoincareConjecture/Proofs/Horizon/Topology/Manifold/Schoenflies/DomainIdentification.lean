import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Bounded
import Mathlib.Topology.Connected.Basic










set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]



theorem subset_of_isPreconnected_of_disjoint_frontier
    {U V : Set X} (hU : IsOpen U) (hV : IsPreconnected V)
    (hfront : Disjoint V (frontier U)) (hmeet : (V ∩ U).Nonempty) :
    V ⊆ U := by
  apply hV.subset_left_of_subset_union hU isClosed_closure.isOpen_compl
  · exact disjoint_left.mpr fun x hx hx' => hx' (subset_closure hx)
  · intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr fun hxcl => Set.disjoint_left.mp hfront hx
        (by rw [hU.frontier_eq]; exact ⟨hxcl, hxU⟩)
  · exact hmeet



theorem eq_side_of_frontier_partition
    {Omega S A B : Set X} (hOmega : IsOpen Omega)
    (hconn : IsConnected Omega) (hfront : frontier Omega = S)
    (hA : IsOpen A) (hB : IsOpen B)
    (hcA : IsPreconnected A) (hcB : IsPreconnected B)
    (hdis : Disjoint A B) (hcover : A ∪ B = Sᶜ) :
    Omega = A ∨ Omega = B := by
  have hsub : Omega ⊆ A ∪ B := by
    rw [hcover, ← hfront]
    intro x hx hxf
    rw [hOmega.frontier_eq] at hxf
    exact hxf.2 hx
  have hav : Disjoint A (frontier Omega) := by
    apply disjoint_left.mpr
    intro x hx hxf
    have hxS : x ∈ Sᶜ := hcover ▸ (Or.inl hx : x ∈ A ∪ B)
    exact hxS (hfront ▸ hxf)
  have hbv : Disjoint B (frontier Omega) := by
    apply disjoint_left.mpr
    intro x hx hxf
    have hxS : x ∈ Sᶜ := hcover ▸ (Or.inr hx : x ∈ A ∪ B)
    exact hxS (hfront ▸ hxf)
  rcases hconn.isPreconnected.subset_or_subset hA hB hdis hsub with ha | hb
  · left
    apply Subset.antisymm ha
    apply subset_of_isPreconnected_of_disjoint_frontier hOmega hcA hav
    obtain ⟨x, hx⟩ := hconn.nonempty
    exact ⟨x, ha hx, hx⟩
  · right
    apply Subset.antisymm hb
    apply subset_of_isPreconnected_of_disjoint_frontier hOmega hcB hbv
    obtain ⟨x, hx⟩ := hconn.nonempty
    exact ⟨x, hb hx, hx⟩


theorem eq_bounded_side_of_frontier_partition
    {E : Type*} [NormedAddCommGroup E] {Omega S A B : Set E}
    (hOmega : IsOpen Omega) (hconn : IsConnected Omega)
    (hbounded : Bornology.IsBounded Omega) (hfront : frontier Omega = S)
    (hA : IsOpen A) (hB : IsOpen B)
    (hcA : IsPreconnected A) (hcB : IsPreconnected B)
    (hdis : Disjoint A B) (hcover : A ∪ B = Sᶜ)
    (hBunbounded : ¬Bornology.IsBounded B) : Omega = A := by
  rcases eq_side_of_frontier_partition hOmega hconn hfront hA hB hcA hcB
      hdis hcover with h | h
  · exact h
  · exact (hBunbounded (h ▸ hbounded)).elim

end Poincare.Topology
