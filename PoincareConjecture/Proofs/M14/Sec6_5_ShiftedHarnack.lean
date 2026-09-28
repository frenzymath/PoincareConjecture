import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegral









set_option autoImplicit false

open Set
open scoped intervalIntegral

namespace PoincareConjecture.M14




theorem shiftedHarnack_intervalIntegrable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (H : ℝ → ℝ)
    (hH : IntervalIntegrable (fun t => t * Real.sqrt t * H t) MeasureTheory.volume a b) :
    IntervalIntegrable (fun t => Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 * H t)
      MeasureTheory.volume a b := by
  by_cases ha0 : a = 0
  · apply hH.congr_uIoo
    intro t ht
    rw [uIoo_of_le hab.le] at ht
    have ht0 : 0 ≤ t := ha.trans ht.1.le
    simp only [ha0, Real.sqrt_zero, sub_zero, Real.sq_sqrt ht0]
    ring
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hc : ContinuousOn (fun t => (1 - Real.sqrt a / Real.sqrt t) ^ 2) (uIcc a b) := by
      rw [uIcc_of_le hab.le]
      exact (continuousOn_const.sub (continuousOn_const.div Real.continuous_sqrt.continuousOn
        (fun t ht => (Real.sqrt_pos.mpr (ha'.trans_le ht.1)).ne'))).pow 2
    apply (hH.mul_continuousOn hc).congr_uIoo
    intro t ht
    rw [uIoo_of_le hab.le] at ht
    have ht0 : 0 < t := ha'.trans ht.1
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hquot : 1 - Real.sqrt a / Real.sqrt t =
        (Real.sqrt t - Real.sqrt a) / Real.sqrt t := by
      field_simp [hs]
    dsimp only
    rw [hquot, div_pow, Real.sq_sqrt ht0.le]
    field_simp



theorem shiftedHarnack_integral_square {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (H : ℝ → ℝ) :
    (∫ t in a..b, Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 * H t) =
      ∫ s in Real.sqrt a..Real.sqrt b,
        2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * H (s ^ 2) := by
  have hle := Real.sqrt_le_sqrt hab.le
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt a) (b := Real.sqrt b)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := fun t => Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 * H t)
    (continuous_pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg a).trans hs.1.le))
  rw [Real.sq_sqrt ha, Real.sq_sqrt (ha.trans hab.le)] at hchange
  rw [← hchange]
  apply intervalIntegral.integral_congr_Ioo_of_le hle
  intro s hs
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_sq ((Real.sqrt_nonneg a).trans hs.1.le)]
  ring



theorem shiftedHarnack_square_intervalIntegrable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (H : ℝ → ℝ)
    (hH : IntervalIntegrable (fun t => t * Real.sqrt t * H t) MeasureTheory.volume a b) :
    IntervalIntegrable (fun s => 2 * s ^ 2 * (s - Real.sqrt a) ^ 2 * H (s ^ 2))
      MeasureTheory.volume (Real.sqrt a) (Real.sqrt b) := by
  have hle := Real.sqrt_le_sqrt hab.le
  have hchange := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.sqrt a) (b := Real.sqrt b)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := fun t => Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 * H t)
    (continuous_pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg a).trans hs.1.le))
  rw [Real.sq_sqrt ha, Real.sq_sqrt (ha.trans hab.le)] at hchange
  apply (hchange.mpr (shiftedHarnack_intervalIntegrable ha hab H hH)).congr_uIoo
  intro s hs
  rw [uIoo_of_le hle] at hs
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_sq ((Real.sqrt_nonneg a).trans hs.1.le)]
  ring

end PoincareConjecture.M14
