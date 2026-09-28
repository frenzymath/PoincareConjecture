import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyDisplacement









set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem integral_sq_norm_le_length_sq_energy {f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) (hb : f b = 0) :
    (∫ s in a..b, ‖f s‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ s in a..b, ‖deriv f s‖ ^ 2 := by
  have he : 0 ≤ ∫ s in a..b, ‖deriv f s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) :
      ‖f s‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv f t‖ ^ 2 := by
    have h := norm_sub_sq_le_total_interval_energy hf hdf hd hs
    rw [hb, zero_sub, norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hs.1 b) he)
  have hi : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuous_pow 2).comp_continuousOn hf.norm
  have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hpoint
  simpa only [intervalIntegral.integral_const, smul_eq_mul, pow_two, mul_assoc] using h




theorem eq_zero_of_interval_energy_eq_zero {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) (hb : f b = 0)
    (he : (∫ s in a..b, ‖deriv f s‖ ^ 2) = 0) {s : ℝ} (hs : s ∈ Icc a b) :
    f s = 0 := by
  have h := norm_sub_sq_le_total_interval_energy hf hdf hd hs
  rw [hb, zero_sub, norm_neg, he, mul_zero] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (f s)])

end PoincareConjecture.M14
