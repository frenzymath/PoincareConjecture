import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



set_option autoImplicit false

open Set

namespace Poincare.Analysis



theorem increment_ge_of_concaveOn_sub_quadratic {f : ℝ → ℝ} {L H t : ℝ}
    (hL : 0 < L) (hconc : ConcaveOn ℝ (Icc 0 L) (fun s => f s - H * s ^ 2 / 2))
    (ht : t ∈ Icc 0 L) :
    t / L * (f L - f 0) - H * t * (L - t) / 2 ≤ f t - f 0 := by
  have hfrac : 0 ≤ t / L := div_nonneg ht.1 hL.le
  have hfrac1 : t / L ≤ 1 := (div_le_one hL).mpr ht.2
  have h := hconc.2 (left_mem_Icc.mpr hL.le) (right_mem_Icc.mpr hL.le)
    (show 0 ≤ 1 - t / L by linarith) hfrac (by ring : 1 - t / L + t / L = 1)
  have hpoint : (1 - t / L) • (0 : ℝ) + (t / L) • L = t := by
    simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hL.ne']
  rw [hpoint] at h
  simp only [smul_eq_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    zero_div, sub_zero] at h
  have heq : (1 - t / L) * f 0 + t / L * (f L - H * L ^ 2 / 2) -
      (f t - H * t ^ 2 / 2) =
      (t / L * (f L - f 0) - H * t * (L - t) / 2) - (f t - f 0) := by
    field_simp
    ring
  linarith



theorem mul_lt_increment_of_concaveOn_sub_quadratic {f : ℝ → ℝ} {L H c t : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H)
    (hconc : ConcaveOn ℝ (Icc 0 L) (fun s => f s - H * s ^ 2 / 2))
    (hc : c < (f L - f 0) / L - H * L / 2) (ht : 0 < t) (htL : t ≤ L) :
    c * t < f t - f 0 := by
  have hchord := increment_ge_of_concaveOn_sub_quadratic hL hconc ⟨ht.le, htL⟩
  have hstrict := mul_lt_mul_of_pos_right hc ht
  have hnonneg : 0 ≤ H * t ^ 2 / 2 := by positivity
  have heq : t / L * (f L - f 0) - H * t * (L - t) / 2 =
      ((f L - f 0) / L - H * L / 2) * t + H * t ^ 2 / 2 := by ring
  rw [heq] at hchord
  linarith

end Poincare.Analysis
