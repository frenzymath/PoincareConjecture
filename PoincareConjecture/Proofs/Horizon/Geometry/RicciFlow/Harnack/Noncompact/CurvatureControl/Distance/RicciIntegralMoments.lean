import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegralCutoff
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Integral.ExponentialMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory intervalIntegral

namespace Poincare.RicciIntegral

theorem integral_cutoff_defect_min_quadratic_le {L scale A B : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in 0..L, (1 - cutoff L scale t ^ 2) *
      min (A + B * t ^ 2) (A + B * (L - t) ^ 2)) ≤
      4 * A / scale + 8 * B / scale ^ 3 := by
  let f : ℝ → ℝ := fun t => Real.exp (-scale * t) * (A + B * t ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfr : Continuous (fun t => f (L - t)) := hf.comp (continuous_const.sub continuous_id)
  have hc : Continuous (fun t : ℝ => (1 - cutoff L scale t ^ 2) *
      min (A + B * t ^ 2) (A + B * (L - t) ^ 2)) := by
    have hcut := (contDiff_cutoff L scale).continuous
    fun_prop
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 L) :
      (1 - cutoff L scale t ^ 2) * min (A + B * t ^ 2) (A + B * (L - t) ^ 2) ≤
        2 * (f t + f (L - t)) := by
    let m := min (A + B * t ^ 2) (A + B * (L - t) ^ 2)
    have hm : 0 ≤ m := le_min (by positivity) (by positivity)
    have h := mul_le_mul_of_nonneg_right (cutoff_defect_le hscale.le ht) hm
    have hleft := mul_le_mul_of_nonneg_left (min_le_left (A + B * t ^ 2)
      (A + B * (L - t) ^ 2)) (Real.exp_nonneg (-scale * t))
    have hright := mul_le_mul_of_nonneg_left (min_le_right (A + B * t ^ 2)
      (A + B * (L - t) ^ 2)) (Real.exp_nonneg (-scale * (L - t)))
    dsimp only [f, m] at *
    nlinarith
  calc
    _ ≤ ∫ t : ℝ in 0..L, 2 * (f t + f (L - t)) :=
      intervalIntegral.integral_mono_on hL (hc.intervalIntegrable 0 L)
        (((hf.add hfr).const_mul 2).intervalIntegrable 0 L) hpoint
    _ = 4 * ∫ t : ℝ in 0..L, f t := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hf.intervalIntegrable 0 L) (hfr.intervalIntegrable 0 L),
        intervalIntegral.integral_comp_sub_left f L]
      simp only [sub_self, sub_zero]
      ring
    _ ≤ 4 * (A / scale + 2 * B / scale ^ 3) :=
      mul_le_mul_of_nonneg_left
        (Poincare.Analysis.integral_exp_neg_mul_quadratic_le hL hscale hA hB) (by norm_num)
    _ = _ := by ring

end Poincare.RicciIntegral
