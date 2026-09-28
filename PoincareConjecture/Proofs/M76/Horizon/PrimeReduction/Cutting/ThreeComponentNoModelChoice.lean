import Mathlib.Data.Bool.Basic

set_option autoImplicit false

namespace PoincareConjecture.M76

theorem exists_three_component_no_model_choice
    {A : Type*} (M : A → Prop) (C : A) (D : Bool → A)
    (hseparate : D false ≠ D true → ¬ (M (D false) ∧ M (D true)))
    (hother : C ≠ D false → C ≠ D true → ¬ M C) :
    ∃ b : Bool, (C = D b ∨ ¬ M C ∨ ¬ M (D b)) ∧
      (D (!b) = C ∨ D (!b) = D b ∨ ¬ M (D (!b))) := by
  classical
  by_cases h0 : C = D false
  · by_cases h1 : C = D true
    · exact ⟨false, Or.inl h0, Or.inl h1.symm⟩
    · refine ⟨true, ?_, Or.inl h0.symm⟩
      by_cases hm : M C
      · exact Or.inr (Or.inr (fun hmt => hseparate (by simpa [← h0] using h1)
          ⟨h0 ▸ hm, hmt⟩))
      · exact Or.inr (Or.inl hm)
  · by_cases h1 : C = D true
    · refine ⟨false, ?_, Or.inl h1.symm⟩
      by_cases hm : M C
      · exact Or.inr (Or.inr (fun hmf => hseparate (by
          intro h; exact h0 (h1.trans h.symm)) ⟨hmf, h1 ▸ hm⟩))
      · exact Or.inr (Or.inl hm)
    · have hn := hother h0 h1
      by_cases hd : D false = D true
      · exact ⟨false, Or.inr (Or.inl hn), Or.inr (Or.inl hd.symm)⟩
      · by_cases hm : M (D false)
        · exact ⟨false, Or.inr (Or.inl hn), Or.inr (Or.inr
            (fun hmt => hseparate hd ⟨hm, hmt⟩))⟩
        · exact ⟨true, Or.inr (Or.inl hn), Or.inr (Or.inr hm)⟩

end PoincareConjecture.M76
