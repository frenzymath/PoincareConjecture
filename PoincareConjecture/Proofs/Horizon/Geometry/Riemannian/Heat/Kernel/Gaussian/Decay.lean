import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace PoincareConjecture.LeviCivitaData

open Filter Set
open scoped Topology

theorem gaussian_bound_of_smooth_weight_bounds {I V d r t : ℝ} (ht : 0 < t)
    (hbound : ∀ a : ℝ, 0 ≤ a → ∀ ε : ℝ, 0 < ε →
      I ≤ V * Real.exp ((2 * a) ^ 2 * t + a * (r + ε) - a * (d - r - ε))) :
    I ≤ V * Real.exp (-(max (d - 2 * r) 0) ^ 2 / (16 * t)) := by
  have hzero (a : ℝ) (ha : 0 ≤ a) :
      I ≤ V * Real.exp ((2 * a) ^ 2 * t - a * (d - 2 * r)) := by
    have hc : Continuous (fun ε : ℝ =>
        V * Real.exp ((2 * a) ^ 2 * t + a * (r + ε) - a * (d - r - ε))) := by
      fun_prop
    have hl := hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have h := ge_of_tendsto hl
      (mem_of_superset self_mem_nhdsWithin (fun ε hε => hbound a ha ε hε))
    convert h using 1 <;> congr 2 <;> ring
  by_cases hsep : 0 ≤ d - 2 * r
  · rw [max_eq_left hsep]
    have ha : 0 ≤ (d - 2 * r) / (8 * t) := div_nonneg hsep (by positivity)
    have h := hzero ((d - 2 * r) / (8 * t)) ha
    convert h using 1 <;> congr 2 <;> field_simp <;> ring
  · rw [max_eq_right (le_of_not_ge hsep)]
    simpa using hzero 0 le_rfl

private theorem sq_max_sub_two_sqrt_lower_bound {d t : ℝ}
    (hd : 0 ≤ d) (ht : 0 < t) :
    d ^ 2 / 2 - 4 * t ≤ (max (d - 2 * Real.sqrt t) 0) ^ 2 := by
  have hsqrt := Real.sq_sqrt ht.le
  by_cases hsep : 0 ≤ d - 2 * Real.sqrt t
  · rw [max_eq_left hsep]
    nlinarith [sq_nonneg (d - 4 * Real.sqrt t)]
  · rw [max_eq_right (le_of_not_ge hsep)]
    have hdsq : d ^ 2 ≤ (2 * Real.sqrt t) ^ 2 :=
      (sq_le_sq₀ hd (by positivity)).mpr (by linarith)
    nlinarith

theorem exp_neg_sq_max_sub_two_sqrt_le {d t : ℝ}
    (hd : 0 ≤ d) (ht : 0 < t) :
    Real.exp (-(max (d - 2 * Real.sqrt t) 0) ^ 2 / (48 * t)) ≤
      Real.exp (1 / 12) * Real.exp (-d ^ 2 / (96 * t)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (by positivity : 0 < 48 * t)).mpr
  have hscale : ((1 / 12 : ℝ) + -d ^ 2 / (96 * t)) * (48 * t) =
      4 * t - d ^ 2 / 2 := by
    field_simp
    ring
  rw [hscale]
  linarith [sq_max_sub_two_sqrt_lower_bound hd ht]

theorem gaussian_bound_of_double_ball_bounds (n : ℕ) {d t V W C h I : ℝ}
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t ≤ 1)
    (hV : 0 < V) (hW : 0 < W) (hC : 0 ≤ C)
    (hbound : h ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) /
      (V * W) * I)
    (hIntegral : I ≤ Real.sqrt V * Real.sqrt W *
      Real.exp (-(max (d - 2 * Real.sqrt t) 0) ^ 2 / (48 * t))) :
    h ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C + 13 / 12) /
      (Real.sqrt V * Real.sqrt W) * Real.exp (-d ^ 2 / (96 * t)) := by
  have hroot : 0 < Real.sqrt V * Real.sqrt W :=
    mul_pos (Real.sqrt_pos.mpr hV) (Real.sqrt_pos.mpr hW)
  have hVW : V * W = (Real.sqrt V * Real.sqrt W) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt hW.le]
  have hexp :
      Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) * Real.exp (1 / 12) =
        Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 13 / 12) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    h ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) / (V * W) *
        (Real.sqrt V * Real.sqrt W *
          Real.exp (-(max (d - 2 * Real.sqrt t) 0) ^ 2 / (48 * t))) :=
      hbound.trans (mul_le_mul_of_nonneg_left hIntegral (by positivity))
    _ = Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) /
        (Real.sqrt V * Real.sqrt W) *
          Real.exp (-(max (d - 2 * Real.sqrt t) 0) ^ 2 / (48 * t)) := by
      rw [hVW]
      field_simp
    _ ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 1) /
        (Real.sqrt V * Real.sqrt W) *
          (Real.exp (1 / 12) * Real.exp (-d ^ 2 / (96 * t))) :=
      mul_le_mul_of_nonneg_left (exp_neg_sq_max_sub_two_sqrt_le hd ht) (by positivity)
    _ = Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C * t + 13 / 12) /
        (Real.sqrt V * Real.sqrt W) * Real.exp (-d ^ 2 / (96 * t)) := by
      rw [← hexp]
      ring
    _ ≤ Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C + 13 / 12) /
        (Real.sqrt V * Real.sqrt W) * Real.exp (-d ^ 2 / (96 * t)) := by
      apply mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) hroot.le)
        (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left ht1 hC]

end PoincareConjecture.LeviCivitaData
