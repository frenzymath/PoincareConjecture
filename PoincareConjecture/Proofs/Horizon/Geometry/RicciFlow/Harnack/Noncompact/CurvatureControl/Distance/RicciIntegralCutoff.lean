import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set MeasureTheory intervalIntegral
open scoped ContDiff

noncomputable section

namespace Poincare.RicciIntegral

def cutoff (L scale t : ℝ) : ℝ :=
  (1 - Real.exp (-scale * t)) * (1 - Real.exp (-scale * (L - t)))

theorem contDiff_cutoff (L scale : ℝ) : ContDiff ℝ ∞ (cutoff L scale) := by
  unfold cutoff
  fun_prop

@[simp] theorem cutoff_zero (L scale : ℝ) : cutoff L scale 0 = 0 := by
  simp [cutoff]

@[simp] theorem cutoff_end (L scale : ℝ) : cutoff L scale L = 0 := by
  simp [cutoff]

theorem hasDerivAt_cutoff (L scale t : ℝ) :
    HasDerivAt (cutoff L scale)
      (scale * (Real.exp (-scale * t) - Real.exp (-scale * (L - t)))) t := by
  have hA := ((hasDerivAt_id t).const_mul (-scale)).exp
  have hB := (((hasDerivAt_id t).const_sub L).const_mul (-scale)).exp
  convert (hA.const_sub 1).mul (hB.const_sub 1) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

theorem cutoff_mem_Icc {L scale t : ℝ} (hscale : 0 ≤ scale) (ht : t ∈ Icc 0 L) :
    cutoff L scale t ∈ Icc 0 1 := by
  have hA : Real.exp (-scale * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hB : Real.exp (-scale * (L - t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht.2])
  have hA0 := (Real.exp_pos (-scale * t)).le
  have hB0 := (Real.exp_pos (-scale * (L - t))).le
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
  · exact (mul_le_mul (show 1 - Real.exp (-scale * t) ≤ 1 by linarith)
      (show 1 - Real.exp (-scale * (L - t)) ≤ 1 by linarith)
      (sub_nonneg.mpr hB) zero_le_one).trans_eq (one_mul 1)

theorem cutoff_defect_le {L scale t : ℝ} (hscale : 0 ≤ scale) (ht : t ∈ Icc 0 L) :
    1 - cutoff L scale t ^ 2 ≤
      2 * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))) := by
  have hphi := cutoff_mem_Icc hscale ht
  have hAB := mul_nonneg (Real.exp_pos (-scale * t)).le
    (Real.exp_pos (-scale * (L - t))).le
  have hlo : 1 - Real.exp (-scale * t) - Real.exp (-scale * (L - t)) ≤ cutoff L scale t := by
    dsimp [cutoff]
    nlinarith
  nlinarith [sq_nonneg (1 - cutoff L scale t)]

private theorem integral_exp_neg_mul_le {L scale : ℝ} (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * t)) ≤ 1 / scale := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hscale.ne')]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  have hpos := (Real.exp_pos (-(scale * L))).le
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  field_simp
  nlinarith

private theorem integral_exp_neg_reflect_le {L scale : ℝ} (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * (L - t))) ≤ 1 / scale := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => Real.exp (-scale * t)) L]
  simpa using (integral_exp_neg_mul_le (L := L) hscale)

theorem integral_cutoff_defect_le {L scale : ℝ} (hL : 0 ≤ L) (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, 1 - cutoff L scale t ^ 2) ≤ 4 / scale := by
  have hA : Continuous (fun t : ℝ => Real.exp (-scale * t)) := by fun_prop
  have hB : Continuous (fun t : ℝ => Real.exp (-scale * (L - t))) := by fun_prop
  have hc := (contDiff_cutoff L scale).continuous
  calc
    (∫ t : ℝ in 0..L, 1 - cutoff L scale t ^ 2) ≤
        ∫ t : ℝ in 0..L, 2 * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))) :=
      intervalIntegral.integral_mono_on hL
        ((continuous_const.sub (hc.pow 2)).intervalIntegrable 0 L)
        (((hA.add hB).const_mul 2).intervalIntegrable 0 L)
        (fun t ht => cutoff_defect_le hscale.le ht)
    _ = 2 * ((∫ t : ℝ in 0..L, Real.exp (-scale * t)) +
        ∫ t : ℝ in 0..L, Real.exp (-scale * (L - t))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hA.intervalIntegrable 0 L) (hB.intervalIntegrable 0 L)]
    _ ≤ 2 * (1 / scale + 1 / scale) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (integral_exp_neg_mul_le hscale) (integral_exp_neg_reflect_le hscale))
        (by norm_num)
    _ = 4 / scale := by ring

theorem deriv_cutoff_sq_le (L scale t : ℝ) :
    deriv (cutoff L scale) t ^ 2 ≤
      2 * scale ^ 2 * (Real.exp (-(2 * scale) * t) + Real.exp (-(2 * scale) * (L - t))) := by
  rw [(hasDerivAt_cutoff L scale t).deriv]
  have hA : Real.exp (-(2 * scale) * t) = Real.exp (-scale * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hB : Real.exp (-(2 * scale) * (L - t)) = Real.exp (-scale * (L - t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hA, hB]
  nlinarith [sq_nonneg (scale * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))))]

theorem integral_deriv_cutoff_sq_le {L scale : ℝ} (hL : 0 ≤ L) (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, deriv (cutoff L scale) t ^ 2) ≤ 2 * scale := by
  have hA : Continuous (fun t : ℝ => Real.exp (-(2 * scale) * t)) := by fun_prop
  have hB : Continuous (fun t : ℝ => Real.exp (-(2 * scale) * (L - t))) := by fun_prop
  have hd := (contDiff_cutoff L scale).continuous_deriv (by simp)
  have h2scale : 0 < 2 * scale := by positivity
  calc
    (∫ t : ℝ in 0..L, deriv (cutoff L scale) t ^ 2) ≤
        ∫ t : ℝ in 0..L,
          2 * scale ^ 2 * (Real.exp (-(2 * scale) * t) + Real.exp (-(2 * scale) * (L - t))) :=
      intervalIntegral.integral_mono_on hL ((hd.pow 2).intervalIntegrable 0 L)
        (((hA.add hB).const_mul (2 * scale ^ 2)).intervalIntegrable 0 L)
        (fun t _ => deriv_cutoff_sq_le L scale t)
    _ = 2 * scale ^ 2 * ((∫ t : ℝ in 0..L, Real.exp (-(2 * scale) * t)) +
        ∫ t : ℝ in 0..L, Real.exp (-(2 * scale) * (L - t))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hA.intervalIntegrable 0 L) (hB.intervalIntegrable 0 L)]
    _ ≤ 2 * scale ^ 2 * (1 / (2 * scale) + 1 / (2 * scale)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (integral_exp_neg_mul_le h2scale) (integral_exp_neg_reflect_le h2scale))
        (by positivity)
    _ = 2 * scale := by field_simp; ring

end Poincare.RicciIntegral
