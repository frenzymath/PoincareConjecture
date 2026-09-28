import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedCover









set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem AlexanderCollarSlab.selected_zero_section_eq
    {S s b k d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (_M : AlexanderCollarSlab S A q β) (hs : s ⊆ S)
    (hB : S ∩ {x | A x = 0} = b ∪ k)
    (_hcap : d ∩ S = b) (hbd : b ⊆ d)
    (hdK : d ∩ k ⊆ {q}) (hq : q ∈ d) :
    (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q}) = (k ∩ s) ∪ {q} := by
  have hkB : k ⊆ S ∩ {x | A x = 0} := subset_union_right.trans hB.symm.subset
  ext x
  constructor
  · rintro (⟨⟨hx | hx, hz⟩, hnd⟩ | hx)
    · have hk : x ∈ k := (hB.subset ⟨hs hx, hz⟩).resolve_left (fun hb => hnd (hbd hb))
      exact Or.inl ⟨hk, hx⟩
    · exact (hnd hx).elim
    · exact Or.inr hx.2
  · rintro (hx | hx)
    · by_cases hxd : x ∈ d
      · have hxq : x = q := hdK ⟨hxd, hx.1⟩
        exact Or.inr ⟨hxd, hxq⟩
      · exact Or.inl ⟨⟨Or.inl hx.2, (hkB hx.1).2⟩, hxd⟩
    · have hxq : x = q := hx
      exact Or.inr ⟨hxq.symm ▸ hq, hx⟩

end Geometry
