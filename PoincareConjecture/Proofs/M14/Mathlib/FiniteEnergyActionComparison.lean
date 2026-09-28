import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyPoincare










set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem finite_energy_action_gap {a b α β : ℝ} (hab : a ≤ b) (hβ : 0 ≤ β)
    {f g L : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (hL : IntervalIntegrable L volume a b)
    (hstationary : (∫ s in a..b, L s) = 0) {w : ℝ → E}
    (hw : ContinuousOn w (Icc a b)) (hwd : DifferentiableOn ℝ w (Ioo a b))
    (hd : MemLp (deriv w) 2 (volume.restrict (Icc a b))) (hb : w b = 0)
    (hpoint : ∀ s ∈ Ioo a b,
      α * ‖deriv w s‖ ^ 2 - β * ‖w s‖ ^ 2 ≤ g s - f s - L s) :
    (α - β * (b - a) ^ 2) * (∫ s in a..b, ‖deriv w s‖ ^ 2) ≤
      (∫ s in a..b, g s) - ∫ s in a..b, f s := by
  have he : IntervalIntegrable (fun s => ‖deriv w s‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd)
  have hp : IntervalIntegrable (fun s => ‖w s‖ ^ 2) volume a b :=
    ((continuous_pow 2).comp_continuousOn hw.norm).intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab
    ((he.const_mul α).sub (hp.const_mul β)) ((hg.sub hf).sub hL) hpoint
  rw [intervalIntegral.integral_sub (he.const_mul α) (hp.const_mul β),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hg.sub hf) hL,
    intervalIntegral.integral_sub hg hf, hstationary, sub_zero] at h
  have hP := mul_le_mul_of_nonneg_left
    (integral_sq_norm_le_length_sq_energy hab hw hwd hd hb) hβ
  nlinarith




theorem finite_energy_action_eq_of_gap_nonpos {a b α β : ℝ}
    (hab : a ≤ b) (hβ : 0 ≤ β) (hshort : 0 < α - β * (b - a) ^ 2)
    {f g L : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (hL : IntervalIntegrable L volume a b)
    (hstationary : (∫ s in a..b, L s) = 0) {w : ℝ → E}
    (hw : ContinuousOn w (Icc a b)) (hwd : DifferentiableOn ℝ w (Ioo a b))
    (hd : MemLp (deriv w) 2 (volume.restrict (Icc a b))) (hb : w b = 0)
    (hpoint : ∀ s ∈ Ioo a b,
      α * ‖deriv w s‖ ^ 2 - β * ‖w s‖ ^ 2 ≤ g s - f s - L s)
    (haction : (∫ s in a..b, g s) ≤ ∫ s in a..b, f s) :
    ∀ s ∈ Icc a b, w s = 0 := by
  have h := finite_energy_action_gap hab hβ hf hg hL hstationary hw hwd hd hb hpoint
  have he : 0 ≤ ∫ s in a..b, ‖deriv w s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg ‖deriv w s‖)
  have hzero : (∫ s in a..b, ‖deriv w s‖ ^ 2) = 0 := by nlinarith
  exact fun _ hs => eq_zero_of_interval_energy_eq_zero hw hwd hd hb hzero hs

end PoincareConjecture.M14
