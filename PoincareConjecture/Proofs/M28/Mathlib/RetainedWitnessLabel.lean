import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

open Filter

theorem Filter.exists_strictMono_constant_label_witness
    {Z : ℕ → Type*} (P label : ∀ k, Z k → Prop)
    (h : ∀ᶠ k in atTop, ∃ z, P k z) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ z : ∀ k, Z (sigma k),
      (∀ k, P (sigma k) (z k)) ∧
      ((∀ k, label (sigma k) (z k)) ∨ (∀ k, ¬ label (sigma k) (z k))) := by
  classical
  have hsplit : ∀ᶠ k in atTop,
      (∃ z, P k z ∧ label k z) ∨ (∃ z, P k z ∧ ¬ label k z) := by
    filter_upwards [h] with k hk
    obtain ⟨z, hz⟩ := hk
    by_cases hl : label k z
    · exact Or.inl ⟨z, hz, hl⟩
    · exact Or.inr ⟨z, hz, hl⟩
  rcases frequently_or_distrib.mp hsplit.frequently with hpos | hneg
  · obtain ⟨sigma, hmono, hgood⟩ := extraction_of_frequently_atTop hpos
    choose z hP hlabel using hgood
    exact ⟨sigma, hmono, z, hP, Or.inl hlabel⟩
  · obtain ⟨sigma, hmono, hgood⟩ := extraction_of_frequently_atTop hneg
    choose z hP hlabel using hgood
    exact ⟨sigma, hmono, z, hP, Or.inr hlabel⟩
