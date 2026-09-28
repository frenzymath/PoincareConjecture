import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real









set_option autoImplicit false

namespace PoincareConjecture.M10


theorem sqrt_det_four_mul_identity (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (((4 * t) • (1 : Matrix (Fin n) (Fin n) ℝ)).det) =
      (2 * Real.sqrt t) ^ n := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hbase : 4 * t = (2 * Real.sqrt t) ^ 2 := by
    nlinarith [Real.sq_sqrt ht]
  rw [hbase, ← pow_mul, Nat.mul_comm 2 n, pow_mul,
    Real.sqrt_sq (pow_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg t)) n)]


theorem rpow_mul_gaussian_jacobian (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.rpow t (-(n : ℝ) / 2) * (2 * Real.sqrt t) ^ n = (2 : ℝ) ^ n := by
  have hpow : Real.rpow t (-(n : ℝ) / 2) = ((Real.sqrt t) ^ n)⁻¹ := by
    conv_lhs => rw [← Real.sq_sqrt ht.le]
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul (Real.sqrt_nonneg t) 2]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring,
      Real.rpow_neg (Real.sqrt_nonneg t), Real.rpow_natCast]
  rw [hpow, mul_pow]
  have hne : (Real.sqrt t) ^ n ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.2 ht).ne'
  field_simp

end PoincareConjecture.M10
