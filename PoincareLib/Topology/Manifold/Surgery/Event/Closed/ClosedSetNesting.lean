import Mathlib.Topology.Connected.Basic

/-!
# Nesting of closed regions with disjoint connected boundaries

The finite sphere-cutting argument for Morgan--Tian Proposition 15.3 uses
this elementary separation step after producing its actual filled balls.
It asserts no existence of a filling for an embedded sphere.
-/

set_option autoImplicit false

open Set Topology

namespace PoincareMT.M38

variable {X : Type*} [TopologicalSpace X] {B C S : Set X}

/-- A preconnected set avoiding a closed region's frontier lies entirely
in its interior or entirely outside the region. -/
theorem preconnected_subset_interior_or_compl
    (hB : IsClosed B) (hS : IsPreconnected S)
    (hdisjoint : Disjoint S (frontier B)) :
    S ⊆ interior B ∨ S ⊆ Bᶜ := by
  apply IsPreconnected.subset_or_subset isOpen_interior hB.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) ?_ hS
  intro x hx
  by_cases hxB : x ∈ B
  · left
    by_contra hxI
    exact Set.disjoint_left.mp hdisjoint hx (hB.frontier_eq ▸ ⟨hxB, hxI⟩)
  · exact Or.inr hxB

/-- Closed regions with a connected boundary and connected inside and
outside have the four usual nesting alternatives when their frontiers
are disjoint. Only the first region needs both connectedness assumptions. -/
theorem closed_regions_nested_or_disjoint_or_cover
    (hB : IsClosed B) (hC : IsClosed C)
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B ∨ B ∪ C = Set.univ := by
  rcases preconnected_subset_interior_or_compl hB hboundary hdisjoint.symm with
    hinside | houtside
  · have havoid : Disjoint Bᶜ (frontier C) := by
      apply Set.disjoint_left.mpr
      intro x hx hfrontier
      exact hx (interior_subset (hinside hfrontier))
    rcases preconnected_subset_interior_or_compl hC hBout havoid with hcover | hsubset
    · right; right; right
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr (interior_subset (hcover hx))
    · right; right; left
      intro x hx
      by_contra hxB
      exact hsubset hxB hx
  · have havoid : Disjoint B (frontier C) := by
      apply Set.disjoint_left.mpr
      intro x hx hfrontier
      exact houtside hfrontier hx
    rcases preconnected_subset_interior_or_compl hC hBin havoid with hsubset | hsep
    · exact Or.inr (Or.inl (hsubset.trans interior_subset))
    · exact Or.inl (Set.disjoint_left.mpr (fun _ hx hy => hsep hx hy))

/-- A common point outside both regions excludes the whole-space
alternative, leaving exactly nesting or disjointness. -/
theorem closed_regions_nested_or_disjoint
    (hB : IsClosed B) (hC : IsClosed C)
    (hBin : IsPreconnected B) (hBout : IsPreconnected Bᶜ)
    (hboundary : IsPreconnected (frontier C))
    (hdisjoint : Disjoint (frontier B) (frontier C))
    (p : X) (hpB : p ∉ B) (hpC : p ∉ C) :
    Disjoint B C ∨ B ⊆ C ∨ C ⊆ B := by
  rcases closed_regions_nested_or_disjoint_or_cover hB hC hBin hBout
    hboundary hdisjoint with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have hp : p ∈ B ∪ C := h.symm ▸ Set.mem_univ p
    exact (hp.elim hpB hpC).elim

/-- Containment of closed regions with disjoint frontiers is strict at
the outer boundary: the smaller closed region lies in the larger interior. -/
theorem subset_interior_of_subset_of_disjoint_frontiers
    (hB : IsClosed B) (hsubset : B ⊆ C)
    (hdisjoint : Disjoint (frontier B) (frontier C)) :
    B ⊆ interior C := by
  intro x hx
  by_cases hxI : x ∈ interior B
  · exact interior_mono hsubset hxI
  · by_contra hxC
    have hxfrontB : x ∈ frontier B := hB.frontier_eq ▸ ⟨hx, hxI⟩
    have hxfrontC : x ∈ frontier C := ⟨subset_closure (hsubset hx), hxC⟩
    exact Set.disjoint_left.mp hdisjoint hxfrontB hxfrontC

end PoincareMT.M38
