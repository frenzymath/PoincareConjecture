import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic










set_option autoImplicit false

open Set

namespace Set





theorem two_foot_replacement_eq_height_carrier
    {E : Type*} {S₀ S₁ N D d₀ r₀ d₁ r₁ : Set E} {h : E → ℝ} {beta : ℝ}
    (hDN : D ⊆ N) (hS₀ : S₀ ⊆ D) (hS₁ : S₁ ⊆ D)
    (hc₀ : (N ∩ {x | beta ≤ h x}) ∩ S₀ = d₀)
    (hc₁ : (N ∩ {x | beta ≤ h x}) ∩ S₁ = d₁)
    (hfeet : d₀ ∪ d₁ = D ∩ {x | beta ≤ h x})
    (hr₀ : r₀ = d₀ ∩ {x | h x = beta})
    (hr₁ : r₁ = d₁ ∩ {x | h x = beta}) :
    ((S₀ \ (d₀ \ r₀)) ∪ (S₁ \ (d₁ \ r₁))) ∪
        (((N ∩ {x | h x = beta}) ∪ (D ∩ {x | beta ≤ h x})) \
          ((d₀ \ r₀) ∪ (d₁ \ r₁))) =
      ((S₀ ∪ S₁) ∩ {x | h x ≤ beta}) ∪ (N ∩ {x | h x = beta}) := by
  have hcap (S d r : Set E) (hSD : S ⊆ D)
      (hc : (N ∩ {x | beta ≤ h x}) ∩ S = d)
      (hr : r = d ∩ {x | h x = beta}) :
      S \ (d \ r) = S ∩ {x | h x ≤ beta} := by
    ext x
    constructor
    · rintro ⟨hxS, hxnot⟩
      refine ⟨hxS, ?_⟩
      change h x ≤ beta
      apply le_of_not_gt
      intro hxhigh
      have hxd : x ∈ d := hc.subset ⟨⟨hDN (hSD hxS), hxhigh.le⟩, hxS⟩
      apply hxnot
      refine ⟨hxd, ?_⟩
      intro hxr
      exact hxhigh.ne' (hr.subset hxr).2
    · rintro ⟨hxS, hxlow⟩
      refine ⟨hxS, ?_⟩
      rintro ⟨hxd, hxnot⟩
      exact hxnot (hr.symm.subset
        ⟨hxd, le_antisymm hxlow (hc.symm.subset hxd).1.2⟩)
  have hlateral :
      ((N ∩ {x | h x = beta}) ∪ (D ∩ {x | beta ≤ h x})) \
          ((d₀ \ r₀) ∪ (d₁ \ r₁)) = N ∩ {x | h x = beta} := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxnot⟩
      · exact hx
      · rcases hfeet.symm.subset hx with hxd | hxd
        · have hxr : x ∈ r₀ := by
            by_contra hn
            exact hxnot (Or.inl ⟨hxd, hn⟩)
          exact ⟨hDN hx.1, (hr₀.subset hxr).2⟩
        · have hxr : x ∈ r₁ := by
            by_contra hn
            exact hxnot (Or.inr ⟨hxd, hn⟩)
          exact ⟨hDN hx.1, (hr₁.subset hxr).2⟩
    · intro hx
      refine ⟨Or.inl hx, ?_⟩
      rintro (⟨hxd, hxnot⟩ | ⟨hxd, hxnot⟩)
      · exact hxnot (hr₀.symm.subset ⟨hxd, hx.2⟩)
      · exact hxnot (hr₁.symm.subset ⟨hxd, hx.2⟩)
  rw [hcap S₀ d₀ r₀ hS₀ hc₀ hr₀, hcap S₁ d₁ r₁ hS₁ hc₁ hr₁, hlateral,
    union_inter_distrib_right]

end Set
