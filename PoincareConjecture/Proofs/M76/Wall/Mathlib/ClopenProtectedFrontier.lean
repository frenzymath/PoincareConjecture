import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenDomainFrontier

set_option autoImplicit false

open Set

namespace Set

theorem protected_frontiers_of_relative_open
    {X : Type*} [TopologicalSpace X] {P L R S : Set X}
    (hP : IsClosed P) (hL : IsClosed L) (hLP : L ⊆ P)
    (hopen : IsOpen ((Subtype.val : P → X) ⁻¹' L))
    (hBL : frontier R ⊆ L) (hfront : frontier P = frontier R ∪ S)
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' P) =
      (Subtype.val : R → X) ⁻¹' S) :
    frontier L = frontier R ∪ (S ∩ L) ∧
      frontier ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' (S ∩ L) ∧
      interior ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' L ∩
          interior ((Subtype.val : R → X) ⁻¹' P) := by
  obtain ⟨U, hU, hLU⟩ := exists_open_inter_of_relative_open hLP hopen
  have hpre : (Subtype.val : R → X) ⁻¹' L =
      (Subtype.val : R → X) ⁻¹' P ∩ (Subtype.val : R → X) ⁻¹' U := by
    rw [hLU]
    rfl
  refine ⟨?_, ?_, interior_eq_inter_of_eq_inter_open
    (hU.preimage continuous_subtype_val) hpre⟩
  · rw [frontier_eq_inter_of_eq_inter_open hP hL hU hLU, hfront]
    ext x
    constructor
    · rintro ⟨hxL, hxB | hxS⟩
      · exact Or.inl hxB
      · exact Or.inr ⟨hxS, hxL⟩
    · rintro (hxB | ⟨hxS, hxL⟩)
      · exact ⟨hBL hxB, Or.inl hxB⟩
      · exact ⟨hxL, Or.inr hxS⟩
  · rw [frontier_eq_inter_of_eq_inter_open
      (hP.preimage continuous_subtype_val) (hL.preimage continuous_subtype_val)
      (hU.preimage continuous_subtype_val) hpre, hrel]
    ext x
    exact and_comm

end Set
