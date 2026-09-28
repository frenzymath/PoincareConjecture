import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem IsCompact.exists_open_shrinkings_inter_subset
    {A B U V N : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hU : IsOpen U) (hV : IsOpen V) (hN : IsOpen N)
    (hAU : A ⊆ U) (hBV : B ⊆ V) (hAB : A ∩ B ⊆ N) :
    ∃ U' V' : Set X, IsOpen U' ∧ IsOpen V' ∧ A ⊆ U' ∧ B ⊆ V' ∧
      U' ⊆ U ∧ V' ⊆ V ∧ U' ∩ V' ⊆ N := by
  have hAN : IsCompact (A \ N) := hA.inter_right hN.isClosed_compl
  have hBN : IsCompact (B \ N) := hB.inter_right hN.isClosed_compl
  have hdis : Disjoint (A \ N) (B \ N) := by
    apply disjoint_left.mpr
    intro x hxA hxB
    exact hxA.2 (hAB ⟨hxA.1, hxB.1⟩)
  obtain ⟨O, P, hO, hP, hAO, hBP, hOP⟩ :=
    SeparatedNhds.of_isCompact_isCompact hAN hBN hdis
  refine ⟨U ∩ (N ∪ O), V ∩ (N ∪ P), hU.inter (hN.union hO),
    hV.inter (hN.union hP), ?_, ?_, inter_subset_left, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hAU hx, ?_⟩
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (hAO ⟨hx, hxN⟩)
  · intro x hx
    refine ⟨hBV hx, ?_⟩
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (hBP ⟨hx, hxN⟩)
  · rintro x ⟨hxU, hxV⟩
    by_contra hxN
    exact disjoint_left.mp hOP (hxU.2.resolve_left hxN) (hxV.2.resolve_left hxN)

end Set
