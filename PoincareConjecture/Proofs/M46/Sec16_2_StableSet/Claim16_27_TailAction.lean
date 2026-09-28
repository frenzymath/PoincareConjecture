import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedScales
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic









set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.Proofs.M46



theorem seed_square_tail_action_le {tau d H C : ℝ} {density : ℝ → ℝ}
    (htau : 0 ≤ tau) (hd : 0 ≤ d) (hH : tau + d ≤ H) (hC : 0 ≤ C)
    (hint : IntervalIntegrable density volume (Real.sqrt tau) (Real.sqrt (tau + d)))
    (hbound : ∀ s ∈ Ioo (Real.sqrt tau) (Real.sqrt (tau + d)),
      density s ≤ 2 * s ^ 2 * C) :
    (∫ s in Real.sqrt tau..Real.sqrt (tau + d), density s) ≤ Real.sqrt H * d * C := by
  have hab : Real.sqrt tau ≤ Real.sqrt (tau + d) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right hd)
  have hlin : IntervalIntegrable (fun s : ℝ => 2 * s * (Real.sqrt H * C)) volume
      (Real.sqrt tau) (Real.sqrt (tau + d)) :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable _ _
  have hpoint (s : ℝ) (hs : s ∈ Ioo (Real.sqrt tau) (Real.sqrt (tau + d))) :
      density s ≤ 2 * s * (Real.sqrt H * C) := by
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg tau).trans hs.1.le
    have hsH : s ≤ Real.sqrt H := hs.2.le.trans (Real.sqrt_le_sqrt hH)
    have hmul := mul_le_mul_of_nonneg_left hsH (by positivity : 0 ≤ 2 * s * C)
    nlinarith [hbound s hs]
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab hint hlin hpoint
  have heq : (∫ s in Real.sqrt tau..Real.sqrt (tau + d),
      2 * s * (Real.sqrt H * C)) = Real.sqrt H * d * C := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id,
      Real.sq_sqrt (add_nonneg htau hd), Real.sq_sqrt htau]
    ring
  exact h.trans_eq heq



theorem seed_tail_coefficient_bound {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r) :
    seedImageDelay B r *
      (4 * r⁻¹ ^ 2 + 8 * seedImageRadius B r ^ 2 / seedImageDelay B r ^ 2) ≤
        (129 / 512 : ℝ) := by
  have hd := seedImageDelay_pos hB hr
  have hs := seedImageDelay_scalar_short hB hr
  have hk : 8 * seedImageRadius B r ^ 2 / seedImageDelay B r ≤ 1 / 4 := by
    apply (div_le_iff₀ hd).mpr
    linarith [seedImageRadius_sq_le_delay_div hB hr]
  have heq : seedImageDelay B r *
      (4 * r⁻¹ ^ 2 + 8 * seedImageRadius B r ^ 2 / seedImageDelay B r ^ 2) =
        4 * r⁻¹ ^ 2 * seedImageDelay B r +
          8 * seedImageRadius B r ^ 2 / seedImageDelay B r := by
    field_simp [hd.ne']
  rw [heq]
  linarith

end PoincareConjecture.Proofs.M46
