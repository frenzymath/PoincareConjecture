import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter Set Metric
open scoped Topology ComplexConjugate RealInnerProductSpace SchwartzMap

namespace Complex

private theorem integrable_schwartz_div_id (f : 𝓢(ℂ, ℂ)) :
    Integrable (fun z => f z / z) := by
  have hm : AEStronglyMeasurable (fun z => f z / z) volume :=
    (f.continuous.measurable.div measurable_id).aestronglyMeasurable
  have hi : IntegrableOn (fun z => f z / z) (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (C := SchwartzMap.seminorm ℝ 0 0 f)
      (α := 1) (by simp [finrank_real_complex]) (by simp [finrank_real_complex])
    · filter_upwards with z
      rw [norm_div, Real.rpow_neg_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (f.norm_le_seminorm ℝ z) (inv_nonneg.mpr (norm_nonneg _))
    · exact hm
  have ho : IntegrableOn (fun z => f z / z) (ball (0 : ℂ) 1)ᶜ := by
    apply f.integrable.norm.integrableOn.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    have hz' : 1 ≤ ‖z‖ := by simpa using hz
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hz'
  have hu := integrableOn_union.mpr ⟨hi, ho⟩
  simpa using hu

private theorem integrable_moment_schwartz_div_id (f : 𝓢(ℂ, ℂ)) (n : ℕ) :
    Integrable (fun z => ‖z‖ ^ n * ‖f z / z‖) := by
  cases n with
  | zero => simpa using (integrable_schwartz_div_id f).norm
  | succ n =>
    apply (f.integrable_pow_mul volume n).congr
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    rw [norm_div, pow_succ]
    field_simp [norm_ne_zero_iff.mpr hz]

def schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) (z : ℂ) : ℂ :=
  (Real.pi * I)⁻¹ * 𝓕⁻ (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ) z

theorem contDiff_schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzDbarPotential h) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ)) :=
    Real.contDiff_fourier fun n _ => integrable_moment_schwartz_div_id (𝓕 h) n
  change ContDiff ℝ (⊤ : ℕ∞) (fun z => (Real.pi * I)⁻¹ *
    𝓕⁻ (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ) z)
  simpa only [Real.fourierInv_eq_fourier_neg, Function.comp_def] using
    contDiff_const.mul (hf.comp contDiff_neg)

theorem tendsto_schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) :
    Tendsto (schwartzDbarPotential h) (cocompact ℂ) (𝓝 0) := by
  have hf : Tendsto (𝓕 (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ))
      (cocompact ℂ) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact _
  have hn : Tendsto (fun z : ℂ => -z) (cocompact ℂ) (cocompact ℂ) :=
    le_of_eq (Homeomorph.neg ℂ).map_cocompact
  change Tendsto (fun z => (Real.pi * I)⁻¹ *
    𝓕⁻ (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ) z) _ _
  simpa only [Real.fourierInv_eq_fourier_neg, Function.comp_def, mul_zero] using
    (hf.comp hn).const_mul ((Real.pi * I)⁻¹)

private def derivativePair (s : ℂ) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.apply ℝ ℂ 1 +
    s • ContinuousLinearMap.apply ℝ ℂ I)

private theorem derivativePair_apply (s : ℂ) (D : ℂ →L[ℝ] ℂ) :
    derivativePair s D = (D 1 + s * D I) / 2 := by
  simp only [derivativePair, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

private theorem derivativePair_mul (s a : ℂ) (D : ℂ →L[ℝ] ℂ) :
    derivativePair s (a • D) = a * derivativePair s D := by
  simp only [derivativePair_apply, smul_apply, smul_eq_mul]
  ring

private theorem derivativePair_fourierInv (s z : ℂ)
    {g : ℂ → ℂ →L[ℝ] ℂ} (hg : Integrable g) :
    derivativePair s (𝓕⁻ g z) = 𝓕⁻ (fun ξ => derivativePair s (g ξ)) z := by
  have hgi : Integrable (fun ξ => Real.fourierChar (inner ℝ ξ z) • g ξ) := by
    apply hg.norm.mono'
      ((Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const)).aestronglyMeasurable.fun_smul
          hg.aestronglyMeasurable)
    exact Eventually.of_forall fun ξ => (Circle.norm_smul _ (g ξ)).le
  rw [Real.fourierInv_eq, Real.fourierInv_eq,
    ← (derivativePair s).integral_comp_comm hgi]
  apply integral_congr_ae
  filter_upwards with ξ
  simpa only [Circle.smul_def, smul_eq_mul] using
    derivativePair_mul s (Real.fourierChar (inner ℝ ξ z) : ℂ) (g ξ)

private theorem integrable_inverseFrequencyDerivative
    {f : ℂ → ℂ} (hf : Integrable f)
    (hf' : Integrable (fun ξ => ‖ξ‖ * ‖f ξ‖)) :
    Integrable (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) f) := by
  apply (hf'.const_mul (2 * Real.pi * ‖-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
    hf.aestronglyMeasurable.fourierSMulRight
  filter_upwards with ξ
  simpa only [_root_.norm_neg, mul_assoc] using
    VectorFourier.norm_fourierSMulRight_le
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) f ξ

private theorem fderiv_schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) (z : ℂ) :
    fderiv ℝ (schwartzDbarPotential h) z = (Real.pi * I)⁻¹ •
      𝓕⁻ (VectorFourier.fourierSMulRight
        (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
        (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ)) z := by
  have hf := integrable_schwartz_div_id (𝓕 h)
  have hf' : Integrable (fun ξ => ‖ξ‖ * ‖(𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ‖) := by
    simpa using integrable_moment_schwartz_div_id (𝓕 h) 1
  exact ((VectorFourier.hasFDerivAt_fourierIntegral
    (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) hf hf' z).const_smul
    ((Real.pi * I)⁻¹)).fderiv

private theorem derivativePair_inverseFrequency (s ξ : ℂ) (f : ℂ → ℂ) :
    derivativePair s (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) f ξ) =
      (Real.pi * I) * (ξ.re + s * ξ.im) * f ξ := by
  have hx : (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ξ 1 = ξ.re := by
    change (1 * conj ξ).re = ξ.re
    simp
  have hy : (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ξ I = ξ.im := by
    change (I * conj ξ).re = ξ.im
    simp
  simp only [derivativePair_apply, VectorFourier.fourierSMulRight_apply,
    neg_apply, smul_eq_mul, real_smul, hx, hy]
  push_cast
  ring

private theorem fourierInv_const_mul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    𝓕⁻ (fun ξ => a * f ξ) z = a * 𝓕⁻ f z := by
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext ξ
  ring

theorem dbar_schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) (z : ℂ) :
    (fderiv ℝ (schwartzDbarPotential h) z 1 +
      I * fderiv ℝ (schwartzDbarPotential h) z I) / 2 = h z := by
  rw [← derivativePair_apply, fderiv_schwartzDbarPotential, derivativePair_mul]
  have hf' : Integrable (fun ξ => ‖ξ‖ * ‖(𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ‖) := by
    simpa using integrable_moment_schwartz_div_id (𝓕 h) 1
  rw [derivativePair_fourierInv I z
    (integrable_inverseFrequencyDerivative (integrable_schwartz_div_id (𝓕 h)) hf')]
  have hfreq : (fun ξ => derivativePair I (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
      (fun η => (𝓕 h : 𝓢(ℂ, ℂ)) η / η) ξ)) =ᵐ[volume]
      fun ξ => (Real.pi * I) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with ξ hξ
    rw [derivativePair_inverseFrequency, mul_comm I, re_add_im]
    field_simp
  rw [Real.fourierInv_congr_ae hfreq z, fourierInv_const_mul]
  have hinv : 𝓕⁻ (fun ξ => (𝓕 h : 𝓢(ℂ, ℂ)) ξ) z = h z := by
    exact congrFun (h.continuous.fourierInv_fourier_eq h.integrable (𝓕 h).integrable) z
  rw [hinv, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero

theorem dz_schwartzDbarPotential (h : 𝓢(ℂ, ℂ)) (z : ℂ) :
    (fderiv ℝ (schwartzDbarPotential h) z 1 -
      I * fderiv ℝ (schwartzDbarPotential h) z I) / 2 =
        𝓕⁻ (fun ξ => (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ) z := by
  rw [sub_eq_add_neg, ← neg_mul, ← derivativePair_apply]
  rw [fderiv_schwartzDbarPotential, derivativePair_mul]
  have hf' : Integrable (fun ξ => ‖ξ‖ * ‖(𝓕 h : 𝓢(ℂ, ℂ)) ξ / ξ‖) := by
    simpa using integrable_moment_schwartz_div_id (𝓕 h) 1
  rw [derivativePair_fourierInv (-I) z
    (integrable_inverseFrequencyDerivative (integrable_schwartz_div_id (𝓕 h)) hf')]
  have hfreq : (fun ξ => derivativePair (-I) (VectorFourier.fourierSMulRight
      (-(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
      (fun η => (𝓕 h : 𝓢(ℂ, ℂ)) η / η) ξ)) =
      fun ξ => (Real.pi * I) * ((conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ) := by
    funext ξ
    rw [derivativePair_inverseFrequency, RCLike.conj_eq_re_sub_im]
    change _ = (Real.pi * I) * (((ξ.re : ℂ) - ξ.im * I) / ξ * (𝓕 h : 𝓢(ℂ, ℂ)) ξ)
    ring
  rw [hfreq, fourierInv_const_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero

end Complex
