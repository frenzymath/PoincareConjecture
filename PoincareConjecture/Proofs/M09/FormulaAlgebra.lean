import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

theorem residual_identities {n : ℕ} {t l R K d G D : ℝ} (ht : 0 < t)
    (hd : d = R - l / t + K / (2 * t * Real.sqrt t))
    (hG : G = l / t - K / (t * Real.sqrt t) - R) :
    let δ := (n : ℝ) / (2 * t) - R - K / (2 * t * Real.sqrt t) - D
    d + D - ((n : ℝ) / 2 - l) / t = -δ ∧
      d - D + G - R + (n : ℝ) / (2 * t) = δ ∧
      2 * D - G + R + (l - (n : ℝ)) / t = -2 * δ := by
  dsimp only
  rw [hd, hG]
  have ht0 := ne_of_gt ht
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  refine ⟨?_, ?_, ?_⟩ <;> field_simp [ht0, hs0] <;> ring

theorem combined_inequalities {n : ℕ} {t l R K d G D : ℝ} (ht : 0 < t)
    (hd : d = R - l / t + K / (2 * t * Real.sqrt t))
    (hG : G = l / t - K / (t * Real.sqrt t) - R)
    (hD : D ≤ (n : ℝ) / (2 * t) - R - K / (2 * t * Real.sqrt t)) :
    d + D ≤ ((n : ℝ) / 2 - l) / t ∧
      0 ≤ d - D + G - R + (n : ℝ) / (2 * t) ∧
      2 * D - G + R + (l - (n : ℝ)) / t ≤ 0 := by
  obtain ⟨hfirst, hsecond, hthird⟩ := residual_identities ht hd hG (D := D)
  have hδ : 0 ≤ (n : ℝ) / (2 * t) - R - K / (2 * t * Real.sqrt t) - D :=
    sub_nonneg.mpr hD
  refine ⟨?_, ?_, ?_⟩
  · apply sub_nonpos.mp
    rw [hfirst]
    exact neg_nonpos.mpr hδ
  · rw [hsecond]
    exact hδ
  · rw [hthird]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zero_le_two) hδ

end PoincareConjecture.Proofs.M09
