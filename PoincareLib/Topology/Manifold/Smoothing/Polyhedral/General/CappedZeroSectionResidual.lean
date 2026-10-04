import Mathlib.Data.Set.Lattice

/-!
# Exact residual form of a capped zero section

Deleting the selected cap from the zero section and restoring
its marked point leaves exactly the original cut piece's
residual curves and that point. See Alexander 1924, pp. 6--8
and M76 derivation 244.
-/

set_option autoImplicit false

namespace Set

/-- The exact cap-deletion expression is the original residual
intersection with the cut piece, with the marked point adjoined.
This is a set identity and needs no topology or finite-family
premise. See Alexander pp. 6--8 and derivation 244. -/
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
