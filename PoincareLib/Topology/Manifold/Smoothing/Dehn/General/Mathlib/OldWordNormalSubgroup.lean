import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Normal-subgroup word identities for finite crossing surgery

These are the two pure group consequences used by the double-arc
resolutions in Dehn derivation 022, section 11.  They are the exact
normal-subgroup step described in the 2026-09-24 monitor round-36 note
and in Hatcher's double-arc surgery argument.  No disk, crossing or
surgery construction is supplied here.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Dehn

/-- In the first double-arc resolution, membership of both new rim words
`α * γ` and `α * β⁻¹ * γ * δ⁻¹` in a normal subgroup forces membership of
the old word `α * β * γ * δ`.  See Dehn derivation 022, section 11,
case (a), and the monitor round-36 note. -/
theorem old_word_mem_of_case_a {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {α β γ δ : G} (h₁ : α * γ ∈ N) (h₂ : α * β⁻¹ * γ * δ⁻¹ ∈ N) :
    α * β * γ * δ ∈ N := by
  have h₃ : γ⁻¹ * β⁻¹ * γ * δ⁻¹ ∈ N := by
    have h := N.mul_mem (N.inv_mem h₁) h₂
    simpa [mul_assoc, mul_inv_rev] using h
  have h₄ : δ * (γ⁻¹ * β * γ) ∈ N := by
    have h := N.inv_mem h₃
    simpa [mul_assoc, mul_inv_rev] using h
  have h₅ : γ⁻¹ * β * γ * δ ∈ N := by
    have h := Subgroup.Normal.conj_mem' ‹N.Normal› _ h₄ δ
    simpa [mul_assoc] using h
  have hfactor : α * β * γ * δ =
      (α * γ) * (γ⁻¹ * β * γ * δ) := by
    group
  rw [hfactor]
  exact N.mul_mem h₁ h₅

/-- In the second double-arc resolution, membership of the new rim words
`α * γ⁻¹` and `α * δ * γ * β` in a normal subgroup forces membership of
the old word `α * β * γ * δ`.  See Dehn derivation 022, section 11,
case (b), and the monitor round-36 note. -/
theorem old_word_mem_of_case_b {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {α β γ δ : G} (h₁ : α * γ⁻¹ ∈ N) (h₂ : α * δ * γ * β ∈ N) :
    α * β * γ * δ ∈ N := by
  have h₃ : γ * δ * γ * β ∈ N := by
    have h := N.mul_mem (N.inv_mem h₁) h₂
    simpa [mul_assoc, mul_inv_rev] using h
  have h₄ : γ * β * γ * δ ∈ N := by
    have h := Subgroup.Normal.conj_mem' ‹N.Normal› _ h₃ (γ * δ)
    simpa [mul_assoc, mul_inv_rev] using h
  have hfactor : α * β * γ * δ =
      (α * γ⁻¹) * (γ * β * γ * δ) := by
    group
  rw [hfactor]
  exact N.mul_mem h₁ h₄

end PoincareMT.M76.Dehn
