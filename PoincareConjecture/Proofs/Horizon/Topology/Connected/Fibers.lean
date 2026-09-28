import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem subset_of_connected_of_frontier_saturated
    {X : Type*} [TopologicalSpace X] {S C : Set X}
    (hS : IsPreconnected S)
    (hfront : ∀ x ∈ S ∩ frontier C, S ⊆ C)
    (hmeet : (S ∩ C).Nonempty) : S ⊆ C := by
  by_cases hne : (S ∩ frontier C).Nonempty
  · obtain ⟨x, hx⟩ := hne
    exact hfront x hx
  have hnot (x : X) (hx : x ∈ S) : x ∉ frontier C := fun h => hne ⟨x, hx, h⟩
  have hcover : S ⊆ interior C ∪ interior Cᶜ := by
    intro x hx
    rw [← compl_frontier_eq_union_interior]
    exact hnot x hx
  suffices hs : S ⊆ interior C from hs.trans interior_subset
  apply hS.subset_left_of_subset_union (u := interior C) (v := interior Cᶜ)
    isOpen_interior isOpen_interior
  · exact Set.disjoint_left.mpr fun x hx hy =>
      (show x ∉ C from interior_subset hy) (interior_subset hx)
  · exact hcover
  · obtain ⟨x, hx, hxC⟩ := hmeet
    exact ⟨x, hx, (mem_interior_iff_notMem_frontier hxC).mpr (hnot x hx)⟩

theorem eq_image_closed_band_of_frontier_saturated
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]
    (F : X × Real -> Y) {a b : Real}
    (hF : ∀ t ∈ Icc a b, Continuous (fun x => F (x, t)))
    {C : Set Y} (hC : IsPreconnected C) {h : Y -> Real}
    (hh : ContinuousOn h C)
    (hheight : ∀ x t, t ∈ Icc a b -> h (F (x, t)) = t)
    (hcover : C ⊆ F '' (univ ×ˢ Icc a b))
    (ha : a ∈ h '' C) (hb : b ∈ h '' C)
    (hfront : ∀ t ∈ Icc a b, ∀ x, F (x, t) ∈ frontier C ->
      range (fun y => F (y, t)) ⊆ C) :
    C = F '' (univ ×ˢ Icc a b) := by
  apply Subset.antisymm hcover
  rintro y ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
  have htimage : t ∈ h '' C := (hC.image h hh).Icc_subset ha hb ht
  obtain ⟨p, hp, hpt⟩ := htimage
  obtain ⟨⟨q, u⟩, ⟨_, hu⟩, hqp⟩ := hcover hp
  have hut : u = t := (hheight q u hu).symm.trans ((congrArg h hqp).trans hpt)
  subst u
  have hsub : range (fun z => F (z, t)) ⊆ C := by
    apply subset_of_connected_of_frontier_saturated (isPreconnected_range (hF t ht))
    · rintro z ⟨⟨w, rfl⟩, hz⟩
      exact hfront t ht w hz
    · exact ⟨p, ⟨q, hqp⟩, hp⟩
  exact hsub (mem_range_self x)

theorem eq_union_image_closed_band_of_frontier_saturated
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]
    (F : X × Real -> Y) {a b : Real}
    (hF : ∀ t ∈ Icc a b, Continuous (fun x => F (x, t)))
    {C K : Set Y} (hC : IsPreconnected C) {h : Y -> Real}
    (hh : ContinuousOn h C)
    (hheight : ∀ x t, t ∈ Icc a b -> h (F (x, t)) = t)
    (hKC : K ⊆ C) (hKh : ∀ p ∈ K, h p ≤ a)
    (hbottom : range (fun x => F (x, a)) ⊆ K)
    (hcover : C ⊆ K ∪ F '' (univ ×ˢ Icc a b))
    (ha : a ∈ h '' C) (hb : b ∈ h '' C)
    (hfront : ∀ t ∈ Icc a b, ∀ x, F (x, t) ∈ frontier C ->
      range (fun y => F (y, t)) ⊆ C) :
    C = K ∪ F '' (univ ×ˢ Icc a b) := by
  apply Subset.antisymm hcover
  rintro y (hyK | ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩)
  · exact hKC hyK
  by_cases hta : t = a
  · subst t
    exact hKC (hbottom (mem_range_self x))
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  obtain ⟨p, hp, hpt⟩ := (hC.image h hh).Icc_subset ha hb ht
  change h p = t at hpt
  have hpnot : p ∉ K := fun hpK => hat.not_ge (hpt ▸ hKh p hpK)
  obtain ⟨⟨q, u⟩, ⟨_, hu⟩, hqp⟩ := (hcover hp).resolve_left hpnot
  have hut : u = t := (hheight q u hu).symm.trans ((congrArg h hqp).trans hpt)
  subst u
  have hsub : range (fun z => F (z, t)) ⊆ C := by
    apply subset_of_connected_of_frontier_saturated (isPreconnected_range (hF t ht))
    · rintro z ⟨⟨w, rfl⟩, hz⟩
      exact hfront t ht w hz
    · exact ⟨p, ⟨q, hqp⟩, hp⟩
  exact hsub (mem_range_self x)

end Poincare.Topology
