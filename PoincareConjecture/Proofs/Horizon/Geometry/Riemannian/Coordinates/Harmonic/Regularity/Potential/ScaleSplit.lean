import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace Poincare.Parabolic.Interior.Kernel

variable {E : Type*} [NormedAddCommGroup E]

theorem intervalIntegrable_of_threeQuarter_bound {F : ℝ → E} {t A : ℝ}
    (ht : 0 < t) (hF : AEStronglyMeasurable F (volume.restrict (Ioo 0 t)))
    (hbound : ∀ τ ∈ Ioo 0 t, ‖F τ‖ ≤ A * τ ^ (-(3 / 4 : ℝ))) :
    IntervalIntegrable F volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  have hmajor : IntervalIntegrable (fun τ : ℝ => A * τ ^ (-(3 / 4 : ℝ))) volume 0 t :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(3 / 4 : ℝ))).const_mul A
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp hmajor).mono' hF
    ((ae_restrict_mem measurableSet_Ioo).mono fun τ hτ => hbound τ hτ)

private theorem norm_integral_le_of_bound_Ioo [NormedSpace ℝ E]
    {F : ℝ → E} {q : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : IntervalIntegrable F volume a b)
    (hq : IntervalIntegrable q volume a b)
    (hbound : ∀ τ ∈ Ioo a b, ‖F τ‖ ≤ q τ) :
    ‖∫ τ in a..b, F τ‖ ≤ ∫ τ in a..b, q τ :=
  (intervalIntegral.norm_integral_le_integral_norm hab).trans
    (intervalIntegral.integral_mono_on_of_le_Ioo hab hF.norm hq hbound)

private theorem integral_threeQuarter {t : ℝ} :
    (∫ τ : ℝ in 0..t, τ ^ (-(3 / 4 : ℝ))) = 4 * t ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num : -1 < -(3 / 4 : ℝ)))]
  norm_num
  ring

private theorem square_quarter_eq_sqrt {d : ℝ} (hd : 0 < d) :
    (d ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le, Real.sqrt_eq_rpow]
  norm_num

private theorem mul_square_neg_quarter_eq_sqrt {d : ℝ} (hd : 0 < d) :
    d * (d ^ 2) ^ (-(1 / 4 : ℝ)) = Real.sqrt d := by
  have hpow : (d ^ 2) ^ (-(1 / 4 : ℝ)) = d ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
  calc
    _ = d ^ (1 : ℝ) * d ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one, hpow]
    _ = d ^ (1 + -(1 / 2 : ℝ)) := (Real.rpow_add hd _ _).symm
    _ = Real.sqrt d := by norm_num [Real.sqrt_eq_rpow]

theorem norm_integral_le_halfPower_of_two_bounds [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E} {t d A B : ℝ}
    (ht : 0 < t) (hd : 0 < d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioo 0 t)))
    (hshort : ∀ τ ∈ Ioo 0 t, ‖F τ‖ ≤ A * τ ^ (-(3 / 4 : ℝ)))
    (hlong : ∀ τ ∈ Ioo 0 t, ‖F τ‖ ≤ B * d * τ ^ (-(5 / 4 : ℝ))) :
    IntervalIntegrable F volume 0 t ∧
      ‖∫ τ in 0..t, F τ‖ ≤ 4 * (A + B) * Real.sqrt d := by
  have hFi := intervalIntegrable_of_threeQuarter_bound ht hF hshort
  refine ⟨hFi, ?_⟩
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hshorti (s : ℝ) :
      IntervalIntegrable (fun τ : ℝ => A * τ ^ (-(3 / 4 : ℝ))) volume 0 s :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(3 / 4 : ℝ))).const_mul A
  have hshortint (s : ℝ) :
      (∫ τ in 0..s, A * τ ^ (-(3 / 4 : ℝ))) = 4 * A * s ^ (1 / 4 : ℝ) := by
    rw [intervalIntegral.integral_const_mul, integral_threeQuarter]
    ring
  by_cases htd : t ≤ d ^ 2
  · calc
      _ ≤ ∫ τ in 0..t, A * τ ^ (-(3 / 4 : ℝ)) :=
        norm_integral_le_of_bound_Ioo ht.le hFi (hshorti t) hshort
      _ = 4 * A * t ^ (1 / 4 : ℝ) := hshortint t
      _ ≤ 4 * A * (d ^ 2) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le htd (by norm_num)) (by positivity)
      _ = 4 * A * Real.sqrt d := by rw [square_quarter_eq_sqrt hd]
      _ ≤ 4 * (A + B) * Real.sqrt d := by gcongr; exact le_add_of_nonneg_right hB
  · have hdt : d ^ 2 < t := lt_of_not_ge htd
    have hFi0 : IntervalIntegrable F volume 0 (d ^ 2) := by
      apply hFi.mono_set
      rw [uIcc_of_le hd2.le, uIcc_of_le ht.le]
      exact Icc_subset_Icc le_rfl hdt.le
    have hFi1 : IntervalIntegrable F volume (d ^ 2) t := by
      apply hFi.mono_set
      rw [uIcc_of_le hdt.le, uIcc_of_le ht.le]
      exact Icc_subset_Icc hd2.le le_rfl
    have hlongi :
        IntervalIntegrable (fun τ : ℝ => B * d * τ ^ (-(5 / 4 : ℝ))) volume (d ^ 2) t := by
      apply IntervalIntegrable.const_mul
      apply intervalIntegral.intervalIntegrable_rpow
      right
      rw [uIcc_of_le hdt.le]
      exact fun h => (not_le_of_gt hd2) h.1
    have hhead : ‖∫ τ in 0..d ^ 2, F τ‖ ≤ 4 * A * Real.sqrt d := by
      calc
        _ ≤ ∫ τ in 0..d ^ 2, A * τ ^ (-(3 / 4 : ℝ)) :=
          norm_integral_le_of_bound_Ioo hd2.le hFi0 (hshorti (d ^ 2))
            (fun τ hτ => hshort τ ⟨hτ.1, hτ.2.trans hdt⟩)
        _ = _ := by rw [hshortint, square_quarter_eq_sqrt hd]
    have htail : ‖∫ τ in d ^ 2..t, F τ‖ ≤ 4 * B * Real.sqrt d := by
      calc
        _ ≤ ∫ τ in d ^ 2..t, B * d * τ ^ (-(5 / 4 : ℝ)) :=
          norm_integral_le_of_bound_Ioo hdt.le hFi1 hlongi
            (fun τ hτ => hlong τ ⟨hd2.trans hτ.1, hτ.2⟩)
        _ = 4 * B * d * ((d ^ 2) ^ (-(1 / 4 : ℝ)) - t ^ (-(1 / 4 : ℝ))) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
          · norm_num
            ring
          · rw [uIcc_of_le hdt.le]
            exact fun h => (not_le_of_gt hd2) h.1
        _ ≤ 4 * B * d * (d ^ 2) ^ (-(1 / 4 : ℝ)) := by
          gcongr
          exact sub_le_self _ (Real.rpow_nonneg ht.le _)
        _ = 4 * B * Real.sqrt d := by
          rw [mul_assoc (4 * B), mul_square_neg_quarter_eq_sqrt hd]
    rw [← intervalIntegral.integral_add_adjacent_intervals hFi0 hFi1]
    exact (norm_add_le _ _).trans ((add_le_add hhead htail).trans_eq (by ring))

end Poincare.Parabolic.Interior.Kernel
