import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false

namespace Poincare.MeasureTheory.GaussianMoment

theorem summable_weight (k : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ k *
      Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c)) := by
  let M := B + 1 + c * (B + 1) ^ 2 / 4
  have hs : Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ k * Real.exp (-((j : ℝ) + 1))) := by
    simpa using (summable_nat_add_iff 1).mpr
      (Real.summable_pow_mul_exp_neg_nat_mul k (show (0 : ℝ) < 1 by norm_num))
  apply (hs.mul_left (Real.exp M)).of_nonneg_of_le (fun _ ↦ by positivity)
  intro j
  have hquad : B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c ≤ M - ((j : ℝ) + 1) := by
    apply (le_sub_iff_add_le).mpr
    dsimp [M]
    have hsq := sq_nonneg ((j : ℝ) - c * (B + 1) / 2)
    have heq : (j : ℝ) ^ 2 / c * c = (j : ℝ) ^ 2 := div_mul_cancel₀ _ hc.ne'
    nlinarith
  calc
    _ ≤ ((j : ℝ) + 1) ^ k * Real.exp (M - ((j : ℝ) + 1)) := by gcongr
    _ = Real.exp M * (((j : ℝ) + 1) ^ k * Real.exp (-((j : ℝ) + 1))) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem tsum_weight_pos (k : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < ∑' j : ℕ, ((j : ℝ) + 1) ^ k *
      Real.exp (B * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / c) := by
  exact (summable_weight k B hc).tsum_pos (fun _ ↦ by positivity) 0 (by positivity)

end Poincare.MeasureTheory.GaussianMoment
