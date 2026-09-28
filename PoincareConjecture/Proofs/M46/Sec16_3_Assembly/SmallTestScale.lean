import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration










set_option autoImplicit false

namespace PoincareConjecture.Proofs.M46


noncomputable def smallTestRadius (B r : ℝ) : ℝ := r / (32 * B)


theorem smallTestRadius_pos {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    0 < smallTestRadius B r :=
  div_pos hr (mul_pos (by norm_num) (zero_lt_one.trans_le hB))


theorem smallTestRadius_le {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    smallTestRadius B r ≤ r := by
  unfold smallTestRadius
  apply (div_le_iff₀ (by positivity : 0 < 32 * B)).mpr
  nlinarith



theorem twice_smallTestRadius_le {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    2 * smallTestRadius B r ≤ r / (8 * B) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  unfold smallTestRadius
  field_simp
  nlinarith


theorem smallTestRadius_sq_le {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    smallTestRadius B r ^ 2 ≤ r ^ 2 / (64 * B) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  unfold smallTestRadius
  apply (le_div_iff₀ (by positivity : 0 < 64 * B)).mpr
  field_simp
  nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hB)]


theorem fifty_two_inv_sq_le_smallTestRadius_inv_sq {B r : ℝ}
    (hB : 1 ≤ B) (hr : 0 < r) :
    52 * r⁻¹ ^ 2 ≤ (smallTestRadius B r)⁻¹ ^ 2 := by
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hi : 0 ≤ r⁻¹ ^ 2 := (sq_pos_of_pos (inv_pos.mpr hr)).le
  have hmul := mul_le_mul_of_nonneg_right hBsq hi
  have hinv : (smallTestRadius B r)⁻¹ = 32 * B * r⁻¹ := by
    simp [smallTestRadius, div_eq_mul_inv]
  rw [hinv, mul_pow, mul_pow]
  nlinarith only [hi, hmul]

end PoincareConjecture.Proofs.M46
