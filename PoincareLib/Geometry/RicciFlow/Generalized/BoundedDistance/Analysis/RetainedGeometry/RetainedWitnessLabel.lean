import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Retaining one label with dependent witnesses

An eventual family of witnesses has a strictly increasing selection on
which one binary label is fixed. The witness may vary at each selected
index. This is the orientation selection in Morgan--Tian Proposition 10.7,
pp. 253-254; M28 derivation 114.
-/

set_option autoImplicit false

open Filter

/-- Choose a strict subsequence, witnesses at every selected index, and
one common binary label. Neither a convergent witness family nor an
eventually constant label is assumed. Source: M28 derivation 114. -/
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
