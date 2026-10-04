import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra of the reduced-length defect

The actual time, gradient and Laplacian formulas give the three
defect identities by substitution. Morgan-Tian Theorem 6.50 and
Corollary 6.51, pp. 131-132.
-/

set_option autoImplicit false

namespace PoincareMT.M14

/-- The three scalar defect identities following from the exact time
and gradient formulas, Theorem 6.50 and Corollary 6.51, pp. 131-132. -/
theorem reducedLength_delta_identities {t : ℝ} (ht : 0 < t)
    (n L R K A B C : ℝ)
    (hA : A = R - L / t + K / (2 * t * Real.sqrt t))
    (hC : C = L / t - K / (t * Real.sqrt t) - R) :
    let d := n / (2 * t) - R - K / (2 * t * Real.sqrt t) - B
    (A + B - (n / 2 - L) / t = -d) ∧
      (A - B + C - R + n / (2 * t) = d) ∧
      (2 * B - C + R + (L - n) / t = -2 * d) := by
  dsimp only
  rw [hA, hC]
  constructor
  · field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
    ring
  constructor
  · field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
    ring
  · field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
    ring

end PoincareMT.M14
