import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring










set_option autoImplicit false

namespace PoincareConjecture



theorem m71ProfileAlgebra_neg (w0 : ℝ) (hw : 0 ≤ w0) :
    let c : ℝ := 2 + w0 / (2 * Real.pi)
    let T : ℝ := (c ^ 4 - 1) / 4
    0 ≤ T ∧
      w0 * Real.rpow ((1 + 4 * T) / (1 + 4 * (0 : ℝ))) ((3 : ℝ) / 4) +
        2 * Real.pi * Real.rpow (1 + 4 * (0 : ℝ)) ((1 : ℝ) / 4) *
          Real.rpow (1 + 4 * T) ((3 : ℝ) / 4) -
        2 * Real.pi * (1 + 4 * T) < 0 := by
  dsimp only
  set c : ℝ := 2 + w0 / (2 * Real.pi)
  set T : ℝ := (c ^ 4 - 1) / 4
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hc : 2 ≤ c := by
    dsimp [c]
    linarith [div_nonneg hw hpi.le]
  have hcpos : 0 < c := by linarith
  have hc4 : 1 ≤ c ^ 4 := one_le_pow₀ (by linarith : 1 ≤ c)
  have hclock : 1 + 4 * T = c ^ 4 := by
    dsimp [T]
    ring
  have hpower : (c ^ (4 : ℕ)) ^ ((3 : ℝ) / 4) = c ^ 3 := by
    rw [← Real.rpow_natCast_mul hcpos.le]
    norm_num
  constructor
  · exact div_nonneg (sub_nonneg.mpr hc4) (by norm_num : (0 : ℝ) ≤ 4)
  · simp only [Real.rpow_eq_pow, mul_zero, add_zero, div_one, Real.one_rpow,
      mul_one, hclock, hpower]
    have hcw : 2 * Real.pi * c = 4 * Real.pi + w0 := by
      dsimp [c]
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hpi)]
      ring
    calc
      w0 * c ^ 3 + 2 * Real.pi * c ^ 3 - 2 * Real.pi * c ^ 4 =
          (w0 + 2 * Real.pi - 2 * Real.pi * c) * c ^ 3 := by ring
      _ = -(2 * Real.pi * c ^ 3) := by rw [hcw]; ring
      _ < 0 := neg_neg_of_pos (mul_pos hpi (pow_pos hcpos 3))

end PoincareConjecture
