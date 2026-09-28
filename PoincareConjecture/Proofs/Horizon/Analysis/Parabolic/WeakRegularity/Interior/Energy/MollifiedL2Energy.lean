import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.L2Approximation

open Set MeasureTheory
open Poincare.Analysis.Convolution
open scoped ContDiff

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem norm_toLp_sq {n : ℕ} {u : Spacetime n → ℝ}
    (hu : MemLp u 2 volume) : ‖hu.toLp u‖ ^ 2 = ∫ y, (u y) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with y hy
  simp [hy, pow_two]

theorem integral_mollifiedValue_sq_le
    {n : ℕ} {u ρ : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) :
    (∫ y, (mollifiedValue u ρ r y) ^ 2) ≤
      (∫ y, ‖ρ y‖) ^ 2 * (∫ y, (u y) ^ 2) := by
  have hη : Continuous (rescaledKernel ρ r) :=
    continuous_const.mul (hρ.comp (continuous_id.const_smul r⁻¹))
  have hηc : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hmass : (∫ y, ‖rescaledKernel ρ r y‖) = ∫ y, ‖ρ y‖ := by
    have he : (fun y => ‖rescaledKernel ρ r y‖) =
        rescaledKernel (fun y => ‖ρ y‖) r := by
      funext y
      simp only [rescaledKernel, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow,
        abs_of_pos hr]
    rw [he, integral_rescaledKernel volume _ hr]
  have hm := memLp_lebesgueConvolution hu hη hηc
  have hb := norm_toLp_lebesgueConvolution_le hu hη hηc
  rw [hmass] at hb
  have hs := mul_self_le_mul_self (norm_nonneg _) hb
  simpa only [← pow_two, mul_pow, norm_toLp_sq hm, norm_toLp_sq hu,
    mollifiedValue] using hs

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
