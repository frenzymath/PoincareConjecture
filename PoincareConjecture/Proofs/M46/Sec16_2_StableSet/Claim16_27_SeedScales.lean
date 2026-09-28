import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallTestScale

set_option autoImplicit false

namespace PoincareConjecture.Proofs.M46

noncomputable def seedCylinderDuration (B r : ℝ) : ℝ := r ^ 2 / (64 * B)

noncomputable def seedImageDelay (B r : ℝ) : ℝ := r ^ 2 / (2048 * B)

noncomputable def seedImageRadius (B r : ℝ) : ℝ := r / (256 * B)

theorem seedCylinderDuration_pos {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    0 < seedCylinderDuration B r := by
  unfold seedCylinderDuration
  positivity

theorem seedImageDelay_pos {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    0 < seedImageDelay B r := by
  unfold seedImageDelay
  positivity

theorem seedImageRadius_pos {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    0 < seedImageRadius B r := by
  unfold seedImageRadius
  positivity

theorem seedImageDelay_lt_duration {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    seedImageDelay B r < seedCylinderDuration B r := by
  have hd := seedCylinderDuration_pos hB hr
  have heq : seedImageDelay B r = seedCylinderDuration B r / 32 := by
    unfold seedImageDelay seedCylinderDuration
    ring
  rw [heq]
  linarith

theorem seedCylinderDuration_le_radius_sq {B r : ℝ} (hB : 1 ≤ B) (_hr : 0 < r) :
    seedCylinderDuration B r ≤ r ^ 2 := by
  unfold seedCylinderDuration
  apply (div_le_iff₀ (by positivity : 0 < 64 * B)).mpr
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hB)]

theorem twice_seedImageRadius_lt_ball_radius {B r : ℝ}
    (hB : 1 ≤ B) (hr : 0 < r) :
    2 * seedImageRadius B r < r / (8 * B) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  unfold seedImageRadius
  field_simp
  nlinarith

theorem seedImageRadius_le {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    seedImageRadius B r ≤ r := by
  unfold seedImageRadius
  apply (div_le_iff₀ (by positivity : 0 < 256 * B)).mpr
  nlinarith

theorem seedImageRadius_sq_le_delay_div {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    seedImageRadius B r ^ 2 ≤ seedImageDelay B r / 32 := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  unfold seedImageRadius seedImageDelay
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
  apply (le_div_iff₀ (by positivity : 0 < 2048 * B)).mpr
  field_simp
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hB)]

theorem seedImageRadius_sq_le_duration {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    seedImageRadius B r ^ 2 ≤ seedCylinderDuration B r := by
  have h := seedImageRadius_sq_le_delay_div hB hr
  have hp := seedImageDelay_pos hB hr
  have hd := seedImageDelay_lt_duration hB hr
  linarith

theorem seedImageDelay_metric_short {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    6 * (52 * r⁻¹ ^ 2) * seedImageDelay B r ≤ 1 / 2 := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have heq : 6 * (52 * r⁻¹ ^ 2) * seedImageDelay B r = 39 / (256 * B) := by
    unfold seedImageDelay
    field_simp [hr.ne', hBpos.ne']
    ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 256 * B)).mpr
  linarith

theorem seedImageRadius_curvature_bound {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    52 * r⁻¹ ^ 2 ≤ (seedImageRadius B r)⁻¹ ^ 2 := by
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hi : 0 ≤ r⁻¹ ^ 2 := (sq_pos_of_pos (inv_pos.mpr hr)).le
  have hmul := mul_le_mul_of_nonneg_right hBsq hi
  have hinv : (seedImageRadius B r)⁻¹ = 256 * B * r⁻¹ := by
    simp [seedImageRadius, div_eq_mul_inv]
  rw [hinv, mul_pow, mul_pow]
  nlinarith only [hi, hmul]

theorem seedImageDelay_scalar_short {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    4 * r⁻¹ ^ 2 * seedImageDelay B r ≤ 1 / 512 := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have heq : 4 * r⁻¹ ^ 2 * seedImageDelay B r = 1 / (512 * B) := by
    unfold seedImageDelay
    field_simp [hr.ne', hBpos.ne']
    ring
  rw [heq]
  apply (div_le_iff₀ (by positivity : 0 < 512 * B)).mpr
  linarith

end PoincareConjecture.Proofs.M46
