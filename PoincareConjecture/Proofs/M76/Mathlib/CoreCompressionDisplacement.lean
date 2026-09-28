import PoincareConjecture.Proofs.M76.Mathlib.CoreRadialCompression
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Module









set_option autoImplicit false

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem norm_coreCompression_sub_le (x y : E) :
    ‖coreCompression x - coreCompression y‖ ≤ 4 * ‖x - y‖ / (1 + max 1 ‖x‖) := by
  let a := 1 + max 1 ‖x‖
  let b := 1 + max 1 ‖y‖
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hbnorm : ‖y‖ ≤ b := by
    have h := le_max_right (1 : ℝ) ‖y‖
    dsimp [b]
    linarith
  have hab : |b - a| ≤ ‖x - y‖ := by
    have h := abs_max_sub_max_le_max (1 : ℝ) ‖y‖ 1 ‖x‖
    have h' : |max 1 ‖y‖ - max 1 ‖x‖| ≤ ‖x - y‖ := h.trans
      (max_le (by simp) (by simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y))
    simpa only [b, a, add_sub_add_left_eq_sub] using h'
  have hinv : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  have hterm : |a⁻¹ - b⁻¹| * ‖y‖ ≤ ‖x - y‖ / a := by
    rw [hinv, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb]
    calc
      |b - a| / (a * b) * ‖y‖ ≤ |b - a| / (a * b) * b :=
        mul_le_mul_of_nonneg_left hbnorm (by positivity)
      _ = |b - a| / a := by field_simp
      _ ≤ ‖x - y‖ / a := div_le_div_of_nonneg_right hab ha.le
  have hbase : ‖a⁻¹ • x - b⁻¹ • y‖ ≤ 2 * ‖x - y‖ / a := by
    calc
      ‖a⁻¹ • x - b⁻¹ • y‖ = ‖a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y‖ := by
        congr 1
        module
      _ ≤ ‖a⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • y‖ := norm_add_le _ _
      _ = a⁻¹ * ‖x - y‖ + |a⁻¹ - b⁻¹| * ‖y‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
      _ ≤ a⁻¹ * ‖x - y‖ + ‖x - y‖ / a := add_le_add le_rfl hterm
      _ = 2 * ‖x - y‖ / a := by ring
  have he : coreCompression x - coreCompression y =
      (2 : ℝ) • (a⁻¹ • x - b⁻¹ • y) := by
    simp only [coreCompression, smul_sub, smul_smul, div_eq_mul_inv, a, b]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * ‖a⁻¹ • x - b⁻¹ • y‖ ≤ 2 * (2 * ‖x - y‖ / a) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = 4 * ‖x - y‖ / (1 + max 1 ‖x‖) := by dsimp [a]; ring




theorem two_div_coreCompression_denom_le_deficit (x : E) :
    2 / (1 + max 1 ‖x‖) ≤ 2 - ‖coreCompression x‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [max_eq_left hx, coreCompression_of_norm_le_one hx]
    norm_num
    linarith
  · have hx1 : 1 ≤ ‖x‖ := le_of_not_ge hx
    have hd : 0 < 1 + ‖x‖ := by positivity
    rw [max_eq_right hx1, coreCompression_of_one_le_norm hx1, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hd)]
    have he : 2 - 2 / (1 + ‖x‖) * ‖x‖ = 2 / (1 + ‖x‖) := by
      field_simp
      ring
    rw [he]



theorem norm_coreCompression_sub_le_deficit (x y : E) :
    ‖coreCompression x - coreCompression y‖ ≤
      2 * ‖x - y‖ * (2 - ‖coreCompression x‖) := by
  calc
    ‖coreCompression x - coreCompression y‖ ≤
        4 * ‖x - y‖ / (1 + max 1 ‖x‖) := norm_coreCompression_sub_le x y
    _ = 2 * ‖x - y‖ * (2 / (1 + max 1 ‖x‖)) := by ring
    _ ≤ 2 * ‖x - y‖ * (2 - ‖coreCompression x‖) :=
      mul_le_mul_of_nonneg_left (two_div_coreCompression_denom_le_deficit x) (by positivity)

end NormedSpace
