import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.FieldSimp









set_option autoImplicit false

open scoped ENNReal

namespace ENNReal



theorem rescaled_power_volume_ratio (V : ℝ≥0∞) (n : ℕ)
    {a q c d : ℝ} (ha : 0 < a) (hq : 0 < q) (hc : 0 ≤ c) (hd : 0 < d) :
    (ENNReal.ofReal (c / q) ^ n * V) / ENNReal.ofReal (a / q) ^ n =
      ENNReal.ofReal (c * d) ^ n * (V / ENNReal.ofReal (d * a) ^ n) := by
  have hreal : (c / q) ^ n / (a / q) ^ n = (c * d) ^ n / (d * a) ^ n := by
    rw [← div_pow, ← div_pow]
    congr 1
    field_simp
  have hcoeff : ENNReal.ofReal (c / q) ^ n / ENNReal.ofReal (a / q) ^ n =
      ENNReal.ofReal (c * d) ^ n / ENNReal.ofReal (d * a) ^ n := by
    calc
      _ = ENNReal.ofReal ((c / q) ^ n / (a / q) ^ n) := by
        rw [ENNReal.ofReal_div_of_pos (pow_pos (div_pos ha hq) n),
          ENNReal.ofReal_pow (div_nonneg hc hq.le),
          ENNReal.ofReal_pow (div_nonneg ha.le hq.le)]
      _ = ENNReal.ofReal ((c * d) ^ n / (d * a) ^ n) := congrArg ENNReal.ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (pow_pos (_root_.mul_pos hd ha) n),
          ENNReal.ofReal_pow (_root_.mul_nonneg hc hd.le),
          ENNReal.ofReal_pow (_root_.mul_nonneg hd.le ha.le)]
  rw [ENNReal.mul_div_right_comm, hcoeff]
  simp only [div_eq_mul_inv]
  ac_rfl

end ENNReal
