import Mathlib.Data.Real.Basic
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.M04

theorem shi_time_window_product_le {K α T : ℝ}
    (hK : 0 < K) (hwindow : T ≤ α / K) :
    K * T ≤ α := by
  have h := (le_div_iff₀ hK).mp hwindow
  simpa [mul_comm] using h

theorem shi_time_window_ratio_pos {K α : ℝ}
    (hK : 0 < K) (hα : 0 < α) :
    0 < α / K := by
  exact div_pos hα hK

theorem shi_half_radius_pos {r : ℝ} (hr : 0 < r) :
    0 < r / 2 := by
  linarith

theorem shi_time_power_pos {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < t ^ ((k : ℝ) / 2) := by
  exact Real.rpow_pos_of_pos ht _

theorem shi_scaled_radius_pos {n : ℕ} {α r : ℝ}
    (hr : 0 < r) :
    0 < Real.exp (-(n : ℝ) * α) * r / 4 := by
  have hexp : 0 < Real.exp (-(n : ℝ) * α) := Real.exp_pos _
  positivity

end PoincareConjecture.M04
