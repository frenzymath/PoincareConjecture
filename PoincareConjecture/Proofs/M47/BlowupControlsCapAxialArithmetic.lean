import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarArithmetic
import Mathlib.Algebra.Order.Ring.Pow

set_option autoImplicit false

namespace PoincareConjecture.M47

theorem cap_axial_normalization_order_factor
    {gamma beta lambda : ℝ}
    (hbeta : 0 < beta) (hupper : beta ≤ 301 / 300)
    (hlower : 1 - 4 * gamma ≤ beta) (hlambda : 0 ≤ lambda)
    (hscale : beta * lambda ^ 2 = 1)
    (k : ℕ) (horder : (k : ℝ) * gamma ≤ 1 / 6) :
    beta ^ 2 * (max 1 lambda) ^ (2 * (k + 2)) ≤ 3 := by
  by_cases hl : lambda ≤ 1
  · rw [max_eq_left hl, one_pow, mul_one]
    nlinarith only [hupper, hbeta]
  · have hl : 1 ≤ lambda := (lt_of_not_ge hl).le
    rw [max_eq_right hl]
    have hbern := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ beta) k
    have hmul := mul_le_mul_of_nonneg_left hlower
      (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)
    have hpower : (1 / 3 : ℝ) ≤ beta ^ k := by
      nlinarith only [hbern, hmul, horder]
    have hid : beta ^ k * (beta ^ 2 * lambda ^ (2 * (k + 2))) = 1 := by
      calc
        _ = (beta * lambda ^ 2) ^ (k + 2) := by rw [mul_pow, pow_add, pow_mul]; ring
        _ = 1 := by rw [hscale, one_pow]
    have hf : 0 ≤ beta ^ 2 * lambda ^ (2 * (k + 2)) :=
      mul_nonneg (sq_nonneg beta) (pow_nonneg hlambda _)
    nlinarith only [hpower, hid, hf]

theorem cap_axial_normalization_zero_factor
    {beta lambda : ℝ} (hbeta : 0 ≤ beta) (hupper : beta ≤ 301 / 300)
    (hscale : beta * lambda ^ 2 = 1) :
    beta ^ 2 * (max 1 lambda) ^ 4 ≤ (301 / 300 : ℝ) ^ 2 := by
  by_cases hl : lambda ≤ 1
  · rw [max_eq_left hl, one_pow, mul_one]
    exact (sq_le_sq₀ hbeta (by norm_num)).mpr hupper
  · rw [max_eq_right (lt_of_not_ge hl).le]
    have hid : beta ^ 2 * lambda ^ 4 = 1 := by
      calc
        _ = (beta * lambda ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hscale]; norm_num
    rw [hid]
    norm_num

theorem cap_axial_normalization_uniform_energy
    {E0 E bound d : ℝ}
    (hE0 : 0 ≤ E0) (hE : E0 ≤ E) (hbound : E ≤ bound)
    (hd : d ^ 2 ≤ (16 / 5 : ℝ) ^ 2 * bound) :
    5 * (301 / 300 : ℝ) ^ 2 * E0 + (5 / 2 : ℝ) * d ^ 2 + 3 * (E - E0) ≤
      36 * bound := by
  have hb0 : 0 ≤ bound := hE0.trans (hE.trans hbound)
  have hzero := mul_le_mul_of_nonneg_left (hE.trans hbound)
    (by norm_num : (0 : ℝ) ≤ 5 * (301 / 300 : ℝ) ^ 2)
  have hscalar := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 5 / 2)
  have htail : 3 * (E - E0) ≤ 3 * bound := by linarith only [hbound, hE0]
  nlinarith only [hzero, hscalar, htail, hb0]

end PoincareConjecture.M47
