import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

open Set

namespace Set





theorem exterior_superlevel_frontier_subsets
    {X : Type*} [TopologicalSpace X] {C L R : Set X}
    (hL : IsClosed L) (hR : IsClosed R) (hLC : L ⊆ C)
    (hRC : R ⊆ interior C) {f : X → ℝ} (hf : ContinuousOn f C) {beta : ℝ}
    (hregion : R = (C \ interior L) ∩ {y | beta ≤ f y}) :
    frontier R ⊆ ((C \ interior L) ∩ {y | f y = beta}) ∪
        (frontier L ∩ {y | beta ≤ f y}) ∧
      frontier (L ∪ R) ⊆ (frontier L ∩ {y | f y ≤ beta}) ∪
        ((C \ interior L) ∩ {y | f y = beta}) := by
  have hmem (y : X) : y ∈ R ↔ y ∈ C \ interior L ∧ beta ≤ f y := by
    rw [hregion]
    rfl
  let O := interior C ∩ f ⁻¹' Ioi beta
  have hO : IsOpen O :=
    (hf.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi
  have hOU : O ⊆ L ∪ R := by
    intro y hy
    by_cases hyL : y ∈ L
    · exact Or.inl hyL
    · exact Or.inr ((hmem y).mpr
        ⟨⟨interior_subset hy.1, fun hi => hyL (interior_subset hi)⟩, le_of_lt hy.2⟩)
  have hOR : O ∩ Lᶜ ⊆ R := by
    intro y hy
    exact (hmem y).mpr
      ⟨⟨interior_subset hy.1.1, fun hi => hy.2 (interior_subset hi)⟩, le_of_lt hy.1.2⟩
  have hOint : O ⊆ interior (L ∪ R) := interior_maximal hOU hO
  have hORint : O ∩ Lᶜ ⊆ interior R :=
    interior_maximal hOR (hO.inter hL.isOpen_compl)
  constructor
  · intro x hx
    have hxR : x ∈ R := hR.frontier_subset hx
    have hxmem := (hmem x).mp hxR
    by_cases heq : f x = beta
    · exact Or.inl ⟨hxmem.1, heq⟩
    · have hhigh : beta < f x := lt_of_le_of_ne hxmem.2 (Ne.symm heq)
      by_cases hxL : x ∈ L
      · exact Or.inr ⟨⟨subset_closure hxL, hxmem.1.2⟩, hxmem.2⟩
      · exact False.elim (hx.2 (hORint ⟨⟨hRC hxR, hhigh⟩, hxL⟩))
  · intro x hx
    by_cases hxR : x ∈ R
    · have hxmem := (hmem x).mp hxR
      have heq : f x = beta := by
        by_contra hne
        have hhigh : beta < f x := lt_of_le_of_ne hxmem.2 (Ne.symm hne)
        exact hx.2 (hOint ⟨hRC hxR, hhigh⟩)
      exact Or.inr ⟨hxmem.1, heq⟩
    · have hxL : x ∈ frontier L := by
        rcases frontier_union_subset L R hx with hxL | hxR'
        · exact hxL.1
        · exact False.elim (hxR (hR.frontier_subset hxR'.2))
      have hsmall : f x ≤ beta := by
        by_contra hn
        exact hxR ((hmem x).mpr
          ⟨⟨hLC (hL.frontier_subset hxL), hxL.2⟩, (lt_of_not_ge hn).le⟩)
      exact Or.inl ⟨hxL, hsmall⟩

end Set
