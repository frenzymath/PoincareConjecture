import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.ordinary_zero_section_eq
    {S s b k d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hs : s ⊆ S) (hqs : q ∈ s)
    (hB : S ∩ {x | A x = 0} = b ∪ k) (hbd : b ⊆ d)
    (hdK : d ∩ k ⊆ {q}) (hqd : q ∉ d) :
    (((s ∪ d) ∩ {x | A x = 0}) \ d) = (k ∩ s) ∪ {q} := by
  have hkB : k ⊆ S ∩ {x | A x = 0} := subset_union_right.trans hB.symm.subset
  have hqk : q ∈ k :=
    (hB.subset ⟨M.apex_mem, M.apex_height⟩).resolve_left (fun hb => hqd (hbd hb))
  have hdisj : Disjoint d k := by
    apply disjoint_left.mpr
    intro x hxd hxk
    have hxq : x = q := hdK ⟨hxd, hxk⟩
    exact hqd (hxq ▸ hxd)
  calc
    (((s ∪ d) ∩ {x | A x = 0}) \ d) = k ∩ s := by
      ext x
      constructor
      · rintro ⟨⟨hx | hx, hz⟩, hnd⟩
        · exact ⟨(hB.subset ⟨hs hx, hz⟩).resolve_left (fun hb => hnd (hbd hb)), hx⟩
        · exact (hnd hx).elim
      · exact fun hx => ⟨⟨Or.inl hx.2, (hkB hx.1).2⟩,
          fun hxd => disjoint_left.mp hdisj hxd hx.1⟩
    _ = (k ∩ s) ∪ {q} := by
      have hqks : ({q} : Set E) ⊆ k ∩ s := singleton_subset_iff.mpr ⟨hqk, hqs⟩
      exact (union_eq_left.mpr hqks).symm

end Geometry
