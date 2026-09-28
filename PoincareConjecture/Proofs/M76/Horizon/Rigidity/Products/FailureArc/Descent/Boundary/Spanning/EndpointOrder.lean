import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Longitudinal

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem spanning_center_endpoint_order
    {E : Type*} {Q₀ Q₁ : Set E} (c : P2 → E) (hdis : Disjoint Q₀ Q₁)
    (hfront : ∀ p ∈ source, c p ∈ Q₀ ∪ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (h0 : (c '' arm 0 ∩ Q₀).Nonempty) (h1 : (c '' arm 0 ∩ Q₁).Nonempty) :
    (c (0, 0) ∈ Q₀ ∧ c (1, 0) ∈ Q₁) ∨ (c (0, 0) ∈ Q₁ ∧ c (1, 0) ∈ Q₀) := by
  have hend {Q : Set E} (hQ : Q ⊆ Q₀ ∪ Q₁) (h : (c '' arm 0 ∩ Q).Nonempty) :
      c (0, 0) ∈ Q ∨ c (1, 0) ∈ Q := by
    obtain ⟨x, ⟨p, hp, rfl⟩, hxQ⟩ := h
    have hpS : p ∈ source := ⟨hp.1, by rw [hp.2]; norm_num⟩
    rcases (hfront p hpS).mp (hQ hxQ) with ht | ht
    · exact Or.inl ((congrArg c (show p = (0, 0) from Prod.ext ht hp.2)) ▸ hxQ)
    · exact Or.inr ((congrArg c (show p = (1, 0) from Prod.ext ht hp.2)) ▸ hxQ)
  rcases hend subset_union_left h0 with h00 | h10
  · rcases hend subset_union_right h1 with h01 | h11
    · exact (disjoint_left.mp hdis h00 h01).elim
    · exact Or.inl ⟨h00, h11⟩
  · rcases hend subset_union_right h1 with h01 | h11
    · exact Or.inr ⟨h01, h10⟩
    · exact (disjoint_left.mp hdis h10 h11).elim

theorem paired_spanning_center_endpoint_order
    {E X : Type*} {S : Set E} (Q : Bool → Set E) (mark : Bool → Set X)
    (f : E → X) (c : Bool → P2 → E)
    (hcS : ∀ i, MapsTo (c i) source S)
    (hQdis : Disjoint (Q false) (Q true)) (hmarkdis : Disjoint (mark false) (mark true))
    (hmark : ∀ i, MapsTo f (S ∩ Q i) (mark i))
    (hfront : ∀ i p, p ∈ source → (c i p ∈ Q false ∪ Q true ↔ p.1 = 0 ∨ p.1 = 1))
    (hpair : ∀ t : I, f (c false (t, 0)) = f (c true (t, 0)))
    (h0 : (c false '' arm 0 ∩ Q false).Nonempty)
    (h1 : (c false '' arm 0 ∩ Q true).Nonempty) :
    (∀ j, c j (0, 0) ∈ Q false ∧ c j (1, 0) ∈ Q true) ∨
      (∀ j, c j (0, 0) ∈ Q true ∧ c j (1, 0) ∈ Q false) := by
  have hmate (b : Bool) (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
      (h : c false (t, 0) ∈ Q b) : c true (t, 0) ∈ Q b := by
    have hp : ((t : ℝ), 0) ∈ source := ⟨t.property, by norm_num⟩
    have hm := hmark b ⟨hcS false hp, h⟩
    rw [hpair t] at hm
    have hc := (hfront true _ hp).mpr ht
    cases b
    · exact hc.resolve_right (fun hbad ↦ disjoint_left.mp hmarkdis hm
        (hmark true ⟨hcS true hp, hbad⟩))
    · exact hc.resolve_left (fun hbad ↦ disjoint_left.mp hmarkdis
        (hmark false ⟨hcS true hp, hbad⟩) hm)
  rcases spanning_center_endpoint_order (c false) hQdis (hfront false) h0 h1 with h | h
  · refine Or.inl ?_
    intro j
    cases j
    · exact h
    · exact ⟨hmate false 0 (Or.inl rfl) h.1, hmate true 1 (Or.inr rfl) h.2⟩
  · refine Or.inr ?_
    intro j
    cases j
    · exact h
    · exact ⟨hmate true 0 (Or.inl rfl) h.1, hmate false 1 (Or.inr rfl) h.2⟩

end PoincareConjecture.M76.Dehn
