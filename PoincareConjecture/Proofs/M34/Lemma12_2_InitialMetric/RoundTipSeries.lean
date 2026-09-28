import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false

open FormalMultilinearSeries
open scoped ENNReal Topology

namespace PoincareConjecture.M34

noncomputable def roundTipAngular : ℝ → ℝ :=
  ofScalarsSum (fun n : ℕ => 2 * (-1 : ℝ) ^ n / (2 * n + 2).factorial)

noncomputable def roundTipRadial : ℝ → ℝ :=
  ofScalarsSum (fun n : ℕ => 2 * (-1 : ℝ) ^ n / (2 * n + 4).factorial)

theorem roundTipAngular_zero : roundTipAngular 0 = 1 := by
  norm_num [roundTipAngular, ofScalarsSum_zero]

theorem roundTipRadial_zero : roundTipRadial 0 = 1 / 12 := by
  norm_num [roundTipRadial, ofScalarsSum_zero]

theorem roundTipAngular_radius : (1 : ℝ≥0∞) ≤
    (ofScalars ℝ (fun n : ℕ => 2 * (-1 : ℝ) ^ n / (2 * n + 2).factorial)).radius := by
  apply le_radius_of_bound _ 2 (r := 1)
  intro n
  have hd : (1 : ℝ) ≤ (2 * n + 2).factorial := by
    exact_mod_cast Nat.factorial_pos (2 * n + 2)
  simp only [ofScalars_norm, NNReal.coe_one, one_pow, mul_one, norm_div, norm_mul,
    norm_pow, norm_neg, norm_one, norm_natCast]
  norm_num
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

theorem roundTipRadial_radius : (1 : ℝ≥0∞) ≤
    (ofScalars ℝ (fun n : ℕ => 2 * (-1 : ℝ) ^ n / (2 * n + 4).factorial)).radius := by
  apply le_radius_of_bound _ 2 (r := 1)
  intro n
  have hd : (1 : ℝ) ≤ (2 * n + 4).factorial := by
    exact_mod_cast Nat.factorial_pos (2 * n + 4)
  simp only [ofScalars_norm, NNReal.coe_one, one_pow, mul_one, norm_div, norm_mul,
    norm_pow, norm_neg, norm_one, norm_natCast]
  norm_num
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

theorem roundTipAngular_analyticAt : AnalyticAt ℝ roundTipAngular 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (lt_of_lt_of_le (by norm_num) roundTipAngular_radius)).analyticAt

theorem roundTipRadial_analyticAt : AnalyticAt ℝ roundTipRadial 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (lt_of_lt_of_le (by norm_num) roundTipRadial_radius)).analyticAt

theorem hasSum_roundTipAngular {r : ℝ} (hr : r ≠ 0) :
    HasSum (fun n : ℕ =>
      2 * (-1 : ℝ) ^ n / (2 * n + 2).factorial * (r ^ 2) ^ n)
      (2 * (1 - Real.cos r) / r ^ 2) := by
  have ht : HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ (n + 1) * r ^ (2 * (n + 1)) / (2 * (n + 1)).factorial)
      (Real.cos r - 1) := by
    simpa only [Finset.sum_range_one, mul_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, div_one] using
      (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cos r)
  convert! ht.mul_left (-2 / r ^ 2) using 1
  · ext n
    rw [show 2 * (n + 1) = 2 * n + 2 by omega,
      pow_add r (2 * n) 2, pow_succ (-1 : ℝ) n, ← pow_mul r 2 n]
    field_simp
  · ring

theorem roundTipAngular_sq {r : ℝ} (hr : r ≠ 0) :
    roundTipAngular (r ^ 2) = 2 * (1 - Real.cos r) / r ^ 2 := by
  simpa only [roundTipAngular, ofScalars_sum_eq, smul_eq_mul] using
    (hasSum_roundTipAngular hr).tsum_eq

theorem hasSum_roundTipRadial {r : ℝ} (hr : r ≠ 0) :
    HasSum (fun n : ℕ =>
      2 * (-1 : ℝ) ^ n / (2 * n + 4).factorial * (r ^ 2) ^ n)
      ((1 - roundTipAngular (r ^ 2)) / r ^ 2) := by
  have ht : HasSum (fun n : ℕ =>
      2 * (-1 : ℝ) ^ (n + 1) / (2 * (n + 1) + 2).factorial * (r ^ 2) ^ (n + 1))
      (2 * (1 - Real.cos r) / r ^ 2 - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (hasSum_roundTipAngular hr)
  rw [roundTipAngular_sq hr]
  convert! ht.mul_left (-1 / r ^ 2) using 1
  · ext n
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega]
    simp only [pow_succ]
    field_simp
  · ring

theorem roundTipRadial_sq {r : ℝ} (hr : r ≠ 0) :
    roundTipRadial (r ^ 2) = (1 - roundTipAngular (r ^ 2)) / r ^ 2 := by
  simpa only [roundTipRadial, ofScalars_sum_eq, smul_eq_mul] using
    (hasSum_roundTipRadial hr).tsum_eq

end PoincareConjecture.M34
