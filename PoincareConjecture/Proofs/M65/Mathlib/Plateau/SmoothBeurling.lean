import PoincareConjecture.Proofs.M65.Mathlib.Plateau.FourierL2Integral

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped Topology SchwartzMap ContDiff ComplexConjugate LineDeriv

namespace Complex

private def beurlingFrequency (h : 𝓢(ℂ, ℂ)) (ξ : ℂ) : ℂ :=
  (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ

private theorem measurable_beurlingFrequency (h : 𝓢(ℂ, ℂ)) :
    Measurable (beurlingFrequency h) := by
  unfold beurlingFrequency
  fun_prop

private theorem norm_beurlingFrequency_le (h : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    ‖beurlingFrequency h ξ‖ ≤ ‖(𝓕 h : 𝓢(ℂ, ℂ)) ξ‖ := by
  rw [beurlingFrequency, norm_mul, norm_div, norm_conj]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp [norm_ne_zero_iff.mpr hξ]

private theorem integrable_moment_beurlingFrequency (h : 𝓢(ℂ, ℂ)) (n : ℕ) :
    Integrable (fun ξ => ‖ξ‖ ^ n * ‖beurlingFrequency h ξ‖) := by
  have hm : AEStronglyMeasurable
      (fun ξ => ‖ξ‖ ^ n * ‖beurlingFrequency h ξ‖) volume := by
    exact ((measurable_id.norm.pow_const n).mul
      (measurable_beurlingFrequency h).norm).aestronglyMeasurable
  apply ((𝓕 h).integrable_pow_mul volume n).mono' hm
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (norm_beurlingFrequency_le h ξ)
    (pow_nonneg (norm_nonneg _) _)

private theorem integrable_beurlingFrequency (h : 𝓢(ℂ, ℂ)) :
    Integrable (beurlingFrequency h) := by
  apply ((𝓕 h).integrable (μ := (volume : Measure ℂ))).norm.mono'
    (measurable_beurlingFrequency h).aestronglyMeasurable
  exact Eventually.of_forall (norm_beurlingFrequency_le h)

def beurlingSchwartz (h : 𝓢(ℂ, ℂ)) : ℂ → ℂ := 𝓕⁻ (beurlingFrequency h)

theorem contDiff_beurlingSchwartz (h : 𝓢(ℂ, ℂ)) :
    ContDiff ℝ ∞ (beurlingSchwartz h) := by
  have hf : ContDiff ℝ ∞ (𝓕 (beurlingFrequency h)) :=
    Real.contDiff_fourier fun n _ => integrable_moment_beurlingFrequency h n
  change ContDiff ℝ ∞ (fun z => 𝓕⁻ (beurlingFrequency h) z)
  simpa only [Real.fourierInv_eq_fourier_neg, Function.comp_def] using hf.comp contDiff_neg

theorem beurlingSchwartz_ae (h : 𝓢(ℂ, ℂ)) :
    beurlingSchwartz h =ᵐ[volume] beurlingL2 (h.toLp 2 volume) :=
  (beurlingL2_schwartz_ae h).symm

private theorem integrable_frequencyDerivative (h : 𝓢(ℂ, ℂ)) :
    Integrable (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (beurlingFrequency h)) := by
  have hf' : Integrable (fun ξ => ‖ξ‖ * ‖beurlingFrequency h ξ‖) := by
    simpa using integrable_moment_beurlingFrequency h 1
  apply (hf'.const_mul (2 * Real.pi * ‖-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
    (measurable_beurlingFrequency h).aestronglyMeasurable.fourierSMulRight
  filter_upwards with ξ
  simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le
    (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (beurlingFrequency h) ξ

private theorem frequencyDerivative_apply (h : 𝓢(ℂ, ℂ)) (v ξ : ℂ) :
    VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (beurlingFrequency h) ξ v =
      beurlingFrequency (∂_{v} h) ξ := by
  have hv : (fun η : ℂ => inner ℝ η v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  have hSL : (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ξ v = inner ℝ ξ v := rfl
  rw [beurlingFrequency, SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hv,
    VectorFourier.fourierSMulRight_apply, neg_apply, real_smul, smul_eq_mul,
    beurlingFrequency, hSL]
  push_cast
  ring

theorem fderiv_beurlingSchwartz (h : 𝓢(ℂ, ℂ)) (z v : ℂ) :
    fderiv ℝ (beurlingSchwartz h) z v = beurlingSchwartz (∂_{v} h) z := by
  have hf' : Integrable (fun ξ => ‖ξ‖ * ‖beurlingFrequency h ξ‖) := by
    simpa using integrable_moment_beurlingFrequency h 1
  have hD : HasFDerivAt (beurlingSchwartz h)
      (𝓕⁻ (VectorFourier.fourierSMulRight
        (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (beurlingFrequency h)) z) z :=
    VectorFourier.hasFDerivAt_fourierIntegral
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (integrable_beurlingFrequency h) hf' z
  rw [hD.fderiv, Real.fourierInv_eq_fourier_neg,
    Real.fourier_continuousLinearMap_apply (integrable_frequencyDerivative h)]
  change 𝓕 (fun ξ => VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) (beurlingFrequency h) ξ v) (-z) = _
  simp_rw [frequencyDerivative_apply]
  exact (Real.fourierInv_eq_fourier_neg (beurlingFrequency (∂_{v} h)) z).symm

def localizedBeurling (μ : 𝓢(ℂ, ℂ)) (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (h : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (hμ.mul_right (f' := beurlingSchwartz h)).toSchwartzMap
    ((μ.smooth ⊤).mul (contDiff_beurlingSchwartz h))

theorem localizedBeurling_apply (μ : 𝓢(ℂ, ℂ)) (hμ : HasCompactSupport (μ : ℂ → ℂ))
    (h : 𝓢(ℂ, ℂ)) (z : ℂ) :
    localizedBeurling μ hμ h z = μ z * beurlingSchwartz h z := rfl

theorem norm_localizedBeurling_toLp_le (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hbound : ∀ z, ‖μ z‖ ≤ k)
    (h : 𝓢(ℂ, ℂ)) :
    ‖(localizedBeurling μ hμ h).toLp 2 volume‖ ≤ k * ‖h.toLp 2 volume‖ := by
  have hk : 0 ≤ k := (norm_nonneg (μ 0)).trans (hbound 0)
  calc
    _ ≤ k * ‖beurlingL2 (h.toLp 2 volume)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(localizedBeurling μ hμ h).coeFn_toLp 2 volume,
        beurlingSchwartz_ae h] with z hz hBz
      rw [hz, localizedBeurling_apply, norm_mul, hBz]
      exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_beurlingL2_le _) hk

private theorem hasCompactSupport_lineDeriv (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) (v : ℂ) :
    HasCompactSupport ((∂_{v} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) := by
  exact hμ.fderiv_apply (𝕜 := ℝ) v

theorem lineDeriv_localizedBeurling (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) (h : 𝓢(ℂ, ℂ)) (v : ℂ) :
    ∂_{v} (localizedBeurling μ hμ h) =
      localizedBeurling μ hμ (∂_{v} h) +
        localizedBeurling (∂_{v} μ) (hasCompactSupport_lineDeriv μ hμ v) h := by
  ext z
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => μ y * beurlingSchwartz h y) z v = _
  rw [fderiv_fun_mul μ.differentiableAt
    ((contDiff_beurlingSchwartz h).differentiable (by norm_num)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_beurlingSchwartz,
    localizedBeurling_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

end Complex
