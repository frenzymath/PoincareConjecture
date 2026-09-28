import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.ConvolutionCommutator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Set Filter MeasureTheory MeasureTheory.Measure ContinuousLinearMap
open scoped Topology Convolution ContDiff NNReal

noncomputable section

namespace Poincare.Analysis.Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescaledKernel (ρ : E → ℝ) (r : ℝ) (x : E) : ℝ :=
  (r ^ Module.finrank ℝ E)⁻¹ * ρ (r⁻¹ • x)

theorem integral_rescaledKernel
    (mu : Measure E) [mu.IsAddHaarMeasure] (ρ : E → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ x, rescaledKernel ρ r x ∂mu) = ∫ x, ρ x ∂mu := by
  simp only [rescaledKernel, integral_const_mul]
  rw [integral_comp_inv_smul_of_nonneg mu ρ hr.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem fderiv_rescaledKernel_apply
    {ρ : E → ℝ} (hρ : Differentiable ℝ ρ) (r : ℝ) (x v : E) :
    fderiv ℝ (rescaledKernel ρ r) x v =
      (r ^ (Module.finrank ℝ E + 1))⁻¹ * fderiv ℝ ρ (r⁻¹ • x) v := by
  have hd := ((hρ (r⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r⁻¹)).const_mul ((r ^ Module.finrank ℝ E)⁻¹)
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun y => (r ^ Module.finrank ℝ E)⁻¹ * ρ (r⁻¹ • y)) x v = _
  rw [hd.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, pow_succ, mul_inv_rev]
  ring

theorem integral_firstMoment_derivative_scale
    (mu : Measure E) [mu.IsAddHaarMeasure] (κ : E → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ y, ‖y‖ * |(r ^ (Module.finrank ℝ E + 1))⁻¹ * κ (r⁻¹ • y)| ∂mu) =
      ∫ y, ‖y‖ * |κ y| ∂mu := by
  have hpoint (y : E) :
      ‖y‖ * |(r ^ (Module.finrank ℝ E + 1))⁻¹ * κ (r⁻¹ • y)| =
        (r ^ Module.finrank ℝ E)⁻¹ * (‖r⁻¹ • y‖ * |κ (r⁻¹ • y)|) := by
    simp only [abs_mul, abs_inv, abs_pow, abs_of_pos hr, norm_smul,
      Real.norm_eq_abs, pow_succ, mul_inv_rev]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_comp_inv_smul_of_nonneg mu (fun y => ‖y‖ * |κ y|) hr.le,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

theorem integral_firstMoment_fderiv_rescaledKernel
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {ρ : E → ℝ} (hρ : Differentiable ℝ ρ) {r : ℝ} (hr : 0 < r) (v : E) :
    (∫ y, ‖y‖ * |fderiv ℝ (rescaledKernel ρ r) y v| ∂mu) =
      ∫ y, ‖y‖ * |fderiv ℝ ρ y v| ∂mu := by
  simp_rw [fderiv_rescaledKernel_apply hρ]
  exact integral_firstMoment_derivative_scale mu (fun y => fderiv ℝ ρ y v) hr

theorem abs_derivative_convolution_commutator_rescaled_le
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f ρ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) (v x : E) :
    |q x * ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu] f) x -
      ((fun y => fderiv ℝ (rescaledKernel ρ r) y v) ⋆[lsmul ℝ ℝ, mu]
        (fun y => q y * f y)) x| ≤
      (L : ℝ) * B * ∫ y, ‖y‖ * |fderiv ℝ ρ y v| ∂mu := by
  have hscale : ContDiff ℝ 1 (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hbound := abs_convolution_coefficient_commutator_le mu hq hf hB
    ((hscale.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hcompact.fderiv_apply ℝ v) x
  rw [integral_firstMoment_fderiv_rescaledKernel mu (hρ.differentiable one_ne_zero) hr v]
    at hbound
  exact hbound

theorem abs_convolution_coefficient_commutator_rescaled_le
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f ρ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) (x : E) :
    |q x * (rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] f) x -
      (rescaledKernel ρ r ⋆[lsmul ℝ ℝ, mu] (fun y => q y * f y)) x| ≤
      (L : ℝ) * B * r * ∫ y, ‖y‖ * |ρ y| ∂mu := by
  have hκ : Continuous (rescaledKernel ρ r) := by
    exact (contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))).continuous
  have hκc : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph (Homeomorph.smul
      (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hbase := abs_convolution_coefficient_commutator_le mu hq hf hB hκ hκc x
  have hmoment :
      (∫ y, ‖y‖ * |rescaledKernel ρ r y| ∂mu) =
        r * ∫ y, ‖y‖ * |ρ y| ∂mu := by
    have hpoint (y : E) :
        ‖y‖ * |rescaledKernel ρ r y| =
          (r ^ Module.finrank ℝ E)⁻¹ * r *
            (‖r⁻¹ • y‖ * |ρ (r⁻¹ • y)|) := by
      simp only [rescaledKernel, abs_mul, abs_inv, abs_pow, abs_of_pos hr,
        norm_smul, Real.norm_eq_abs]
      field_simp [hr.ne']
    simp_rw [hpoint]
    rw [integral_const_mul,
      integral_comp_inv_smul_of_nonneg mu
        (fun y => ‖y‖ * |ρ y|) hr.le,
      smul_eq_mul]
    field_simp [hr.ne']
  simpa [hmoment, mul_assoc] using hbase

theorem convolution_coefficient_commutator_rescaled_tendsto_zero
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f ρ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) (x : E) :
    Tendsto (fun n ↦
      |q x * (rescaledKernel ρ (r n) ⋆[lsmul ℝ ℝ, mu] f) x -
        (rescaledKernel ρ (r n) ⋆[lsmul ℝ ℝ, mu]
          (fun y => q y * f y)) x|) atTop (𝓝 0) := by
  let M : ℝ := ∫ y, ‖y‖ * |ρ y| ∂mu
  have hM : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg
    intro y
    positivity
  have hupper : Tendsto (fun n ↦ (L : ℝ) * B * r n * M)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (L : ℝ) * B * M)
        atTop (𝓝 ((L : ℝ) * B * M)) := tendsto_const_nhds
    have hprod := hconst.mul hlim
    convert hprod using 1 <;> simp [mul_assoc, mul_left_comm, mul_comm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [] with n
    exact abs_nonneg _
  · filter_upwards [] with n
    exact abs_convolution_coefficient_commutator_rescaled_le mu hq hf hB
      hρ hρc (hr n) x

end Poincare.Analysis.Convolution
