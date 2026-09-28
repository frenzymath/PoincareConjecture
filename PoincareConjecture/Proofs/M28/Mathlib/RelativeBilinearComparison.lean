import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

set_option autoImplicit false

theorem ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E →L[ℝ] ℝ) {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau)
    (hlower : ∀ v : E, c * ‖v‖ ^ 2 ≤ A v v)
    (herror : ‖B - A‖ ≤ (tau / (1 + tau)) * c) (v : E) :
    (1 + tau)⁻¹ * A v v ≤ B v v ∧ B v v ≤ (1 + tau) * A v v := by
  let d := tau / (1 + tau)
  have hden : 0 < 1 + tau := by linarith
  have hd : 0 ≤ d := (div_pos htau hden).le
  have hdle : d ≤ tau := (div_le_iff₀ hden).mpr (by nlinarith)
  have hidentity : (1 + tau)⁻¹ = 1 - d := by
    dsimp only [d]
    field_simp
    ring
  have hnonneg : 0 ≤ A v v :=
    (mul_nonneg hc.le (sq_nonneg ‖v‖)).trans (hlower v)
  have heval : |B v v - A v v| ≤ d * A v v := by
    calc
      |B v v - A v v| = ‖(B - A) v v‖ := by simp only [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖B - A‖ * ‖v‖ * ‖v‖ := (B - A).le_opNorm₂ v v
      _ ≤ (d * c) * ‖v‖ ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right herror (sq_nonneg ‖v‖)]
      _ = d * (c * ‖v‖ ^ 2) := by ring
      _ ≤ d * A v v := mul_le_mul_of_nonneg_left (hlower v) hd
  have hb := abs_le.mp heval
  constructor
  · rw [hidentity]
    nlinarith only [hb.1]
  · nlinarith only [hb.2, mul_le_mul_of_nonneg_right hdle hnonneg]
