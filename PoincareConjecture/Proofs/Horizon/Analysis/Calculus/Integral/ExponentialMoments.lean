import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory intervalIntegral

namespace Poincare.Analysis

theorem integral_exp_neg_mul_le {L scale : ℝ} (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * t)) ≤ 1 / scale := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hscale.ne')]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  have hpos := (Real.exp_pos (-(scale * L))).le
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  field_simp
  nlinarith

theorem integral_sq_mul_exp_neg_mul_le {L scale : ℝ} (hL : 0 ≤ L) (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, t ^ 2 * Real.exp (-scale * t)) ≤ 2 / scale ^ 3 := by
  let F : ℝ → ℝ := fun t =>
    -Real.exp (-scale * t) * (t ^ 2 / scale + 2 * t / scale ^ 2 + 2 / scale ^ 3)
  have hd (t : ℝ) : HasDerivAt F (t ^ 2 * Real.exp (-scale * t)) t := by
    have he := (((hasDerivAt_id t).const_mul (-scale)).exp).neg
    have hp := ((((hasDerivAt_id t).fun_pow 2).div_const scale).add
      (((hasDerivAt_id t).const_mul 2).div_const (scale ^ 2))).add_const (2 / scale ^ 3)
    convert! he.mul hp using 1
    dsimp only [id_eq, Pi.add_apply, Pi.neg_apply]
    field_simp
    ring
  have hc : Continuous (fun t : ℝ => t ^ 2 * Real.exp (-scale * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 L)]
  have hp : 0 ≤ L ^ 2 / scale + 2 * L / scale ^ 2 + 2 / scale ^ 3 := by positivity
  dsimp only [F]
  simp only [mul_zero, Real.exp_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_div, zero_add]
  nlinarith [mul_nonneg (Real.exp_nonneg (-scale * L)) hp]

theorem integral_exp_neg_mul_quadratic_le {L scale A B : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * t) * (A + B * t ^ 2)) ≤
      A / scale + 2 * B / scale ^ 3 := by
  have he : Continuous (fun t : ℝ => Real.exp (-scale * t)) := by fun_prop
  have hm : Continuous (fun t : ℝ => t ^ 2 * Real.exp (-scale * t)) := by fun_prop
  have heq : (fun t : ℝ => Real.exp (-scale * t) * (A + B * t ^ 2)) =
      (fun t => A * Real.exp (-scale * t) + B * (t ^ 2 * Real.exp (-scale * t))) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add ((he.const_mul A).intervalIntegrable 0 L)
    ((hm.const_mul B).intervalIntegrable 0 L), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (integral_exp_neg_mul_le (L := L) hscale) hA)
    (mul_le_mul_of_nonneg_left (integral_sq_mul_exp_neg_mul_le hL hscale) hB)
  convert! h using 1
  ring

end Poincare.Analysis
