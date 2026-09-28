import Mathlib.Data.Set.Lattice

set_option autoImplicit false

namespace Set

theorem capped_zero_section_eq_residual {X : Type*} {s s' b d R Z : Set X}
    (hsection : (s ∪ s') ∩ Z = b ∪ R) (hbd : b ⊆ d)
    (q : X) (hqd : q ∈ d) (hdR : d ∩ R ⊆ {q}) :
    (((s ∪ d) ∩ Z) \ d) ∪ (d ∩ {q}) = (R ∩ s) ∪ {q} := by
  ext x
  constructor
  · rintro (⟨⟨hxs | hxd, hxZ⟩, hxnd⟩ | hx)
    · have hxR : x ∈ R := (hsection.subset ⟨Or.inl hxs, hxZ⟩).resolve_left
        (fun hxb => hxnd (hbd hxb))
      exact Or.inl ⟨hxR, hxs⟩
    · exact (hxnd hxd).elim
    · exact Or.inr hx.2
  · rintro (hx | hx)
    · by_cases hxd : x ∈ d
      · exact Or.inr ⟨hxd, hdR ⟨hxd, hx.1⟩⟩
      · exact Or.inl ⟨⟨Or.inl hx.2, (hsection.symm.subset (Or.inr hx.1)).2⟩, hxd⟩
    · exact Or.inr ⟨(show x = q from hx).symm ▸ hqd, hx⟩

end Set
