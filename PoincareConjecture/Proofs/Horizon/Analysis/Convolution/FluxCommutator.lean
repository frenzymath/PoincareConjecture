




import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.RescaledKernel
import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.KernelDerivative
import Mathlib.Analysis.Calculus.MeanValue

open Set MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff NNReal

noncomputable section

namespace Poincare.Analysis.Convolution

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]



theorem abs_convolution_le_of_bound
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {κ f : E → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : E) :
    |(κ ⋆[lsmul ℝ ℝ, mu] f) x| ≤ B * ∫ y, |κ y| ∂mu := by
  have hint : Integrable (fun y => κ y * f (x - y)) mu :=
    (hκ.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hκc.mul_right
  have hmajor : Integrable (fun y => B * |κ y|) mu :=
    (hκ.abs.const_mul B).integrable_of_hasCompactSupport hκc.abs.mul_left
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  calc
    |∫ y, κ y * f (x - y) ∂mu| ≤ ∫ y, |κ y * f (x - y)| ∂mu := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := fun y => κ y * f (x - y)) (μ := mu))
    _ ≤ ∫ y, B * |κ y| ∂mu := by
      apply integral_mono_ae hint.norm hmajor
      filter_upwards [] with y
      simpa [abs_mul, mul_comm] using mul_le_mul_of_nonneg_left (hB (x - y)) (abs_nonneg (κ y))
    _ = B * ∫ y, |κ y| ∂mu := integral_const_mul _ _

end NormedGroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem abs_flux_commutator_rescaled_le
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f ρ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hqreg : ContDiff ℝ 1 q) (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) (v x : E) :
    |q x * ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu] f) x -
      ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu]
        (fun y => q y * f y)) x +
      (rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] (fun y => fderiv ℝ q y v * f y)) x| ≤
      (L : ℝ) * B * ((∫ y, ‖y‖ * |fderiv ℝ ρ y v| ∂mu) +
        ‖v‖ * ∫ y, |ρ y| ∂mu) := by
  have hscale : ContDiff ℝ 1 (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hqder (y : E) : |fderiv ℝ q y v| ≤ (L : ℝ) * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using ((fderiv ℝ q y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq) (norm_nonneg v))
  have hprod (y : E) : |fderiv ℝ q y v * f y| ≤ (L : ℝ) * ‖v‖ * B := by
    rw [abs_mul]
    exact mul_le_mul (hqder y) (hB y) (abs_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg v))
  have hcor := abs_convolution_le_of_bound mu hscale.continuous hcompact
    (((hqreg.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hf) hprod x
  have habs : (fun y => |rescaledKernel ρ r y|) = rescaledKernel (fun y => |ρ y|) r := by
    funext y
    simp only [rescaledKernel, abs_mul, abs_inv, abs_pow, abs_of_pos hr]
  rw [habs, integral_rescaledKernel mu _ hr] at hcor
  calc
    _ ≤ |q x * ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu] f) x -
        ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu]
          (fun y => q y * f y)) x| +
        |(rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] (fun y => fderiv ℝ q y v * f y)) x| :=
      abs_add_le _ _
    _ ≤ (L : ℝ) * B * (∫ y, ‖y‖ * |fderiv ℝ ρ y v| ∂mu) +
        ((L : ℝ) * ‖v‖ * B) * ∫ y, |ρ y| ∂mu :=
      add_le_add (abs_derivative_convolution_commutator_rescaled_le mu hq hf hB hρ hρc hr v x)
        hcor
    _ = _ := by ring



theorem abs_mollified_flux_commutator_le
    (mu : Measure E) [mu.IsAddHaarMeasure] [mu.IsNegInvariant]
    {q f ρ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hqreg : ContDiff ℝ 1 q) (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) (v x : E) :
    |q x * fderiv ℝ (rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] f) x v -
      ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu]
        (fun y => q y * f y)) x +
      (rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] (fun y => fderiv ℝ q y v * f y)) x| ≤
      (L : ℝ) * B * ((∫ y, ‖y‖ * |fderiv ℝ ρ y v| ∂mu) +
        ‖v‖ * ∫ y, |ρ y| ∂mu) := by
  have hscale : ContDiff ℝ 1 (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  rw [fderiv_convolution_eq_kernel_derivative mu hf hscale hcompact]
  exact abs_flux_commutator_rescaled_le mu hq hqreg hf hB hρ hρc hr v x

end Poincare.Analysis.Convolution
