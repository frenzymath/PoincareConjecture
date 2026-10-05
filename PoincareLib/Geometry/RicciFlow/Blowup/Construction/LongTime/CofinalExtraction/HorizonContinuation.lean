import Mathlib.Data.ENNReal.Basic

/-!
# Supremum continuation of an attainable horizon

An attainable positive horizon that is closed under cofinal limits and can
be strictly extended below the target reaches the target. The supremum is
taken in the extended nonnegative reals, so the target may be infinite.
The analytic closure and extension hypotheses are separate obligations in
the application to Morgan--Tian Theorem 11.8, pp. 272--279.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace PoincareMT.M30

/-- A positive seed, cofinal-limit closure, and strict extension below the
target imply attainability of the entire target horizon. -/
theorem horizon_of_seed_cofinal_closure_and_extension
    (P : ℝ≥0∞ → Prop) {T0 : ℝ≥0∞}
    (hseed : ∃ T, 0 < T ∧ T ≤ T0 ∧ P T)
    (hclosed : ∀ T, 0 < T → T ≤ T0 →
      (∀ t < T, ∃ U, t < U ∧ U ≤ T ∧ P U) → P T)
    (hextend : ∀ T, 0 < T → T < T0 → P T →
      ∃ U, T < U ∧ U ≤ T0 ∧ P U) : P T0 := by
  let A : Set ℝ≥0∞ := {T | 0 < T ∧ T ≤ T0 ∧ P T}
  let Tstar := sSup A
  obtain ⟨Tseed, hTseed, hTseedT0, hPseed⟩ := hseed
  have hseedA : Tseed ∈ A := ⟨hTseed, hTseedT0, hPseed⟩
  have hstarPos : 0 < Tstar := hTseed.trans_le (le_sSup hseedA)
  have hstarLe : Tstar ≤ T0 := sSup_le fun _ h => h.2.1
  have hPstar : P Tstar := by
    apply hclosed Tstar hstarPos hstarLe
    intro t ht
    obtain ⟨U, hUA, htU⟩ := lt_sSup_iff.mp ht
    exact ⟨U, htU, le_sSup hUA, hUA.2.2⟩
  have hstarEq : Tstar = T0 := by
    by_contra hne
    obtain ⟨U, hstarU, hUT0, hPU⟩ :=
      hextend Tstar hstarPos (lt_of_le_of_ne hstarLe hne) hPstar
    have hUA : U ∈ A := ⟨hstarPos.trans hstarU, hUT0, hPU⟩
    exact (not_lt_of_ge (le_sSup hUA)) hstarU
  exact hstarEq ▸ hPstar

end PoincareMT.M30
