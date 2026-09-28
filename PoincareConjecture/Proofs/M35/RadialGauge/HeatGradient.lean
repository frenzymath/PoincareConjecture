import PoincareConjecture.Proofs.M35.RadialGauge.HeatWeight

set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def gaussianSecondMoment (n : ℕ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))

theorem gaussianSecondMoment_nonneg : 0 ≤ gaussianSecondMoment n :=
  integral_nonneg (fun _ => sq_nonneg _)

noncomputable def heatGradientKernel (t : ℝ) (f : V → F) (x : V) : V →L[ℝ] F :=
  (Real.sqrt (2 * t))⁻¹ • ∫ z,
    (innerSL ℝ z).smulRight (f (x + Real.sqrt (2 * t) • z)) ∂stdGaussian V

theorem heatGradientKernel_integrable {f : V → F} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C) (t : ℝ) (x : V) :
    Integrable (fun z => (innerSL ℝ z).smulRight
      (f (x + Real.sqrt (2 * t) • z))) (stdGaussian V) := by
  have hmoment : Integrable (fun z : V => ‖z‖) (stdGaussian V) :=
    IsGaussian.integrable_id.norm
  have hc : Continuous (fun z : V => (innerSL ℝ z).smulRight
      (f (x + Real.sqrt (2 * t) • z))) := by
    exact ((ContinuousLinearMap.smulRightL ℝ V F).continuous.comp
      (innerSL ℝ).continuous).clm_apply (hf.comp (by fun_prop))
  apply (hmoment.mul_const C).mono' hc.aestronglyMeasurable
  refine Eventually.of_forall (fun z => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  nlinarith [hbound (x + Real.sqrt (2 * t) • z),
    mul_nonneg (norm_nonneg (x + Real.sqrt (2 * t) • z))
      (norm_nonneg (f (x + Real.sqrt (2 * t) • z)))]

theorem heatGradientKernel_weighted_norm_le {f : V → F} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : V) :
    (1 + ‖x‖) * ‖heatGradientKernel t f x‖ ≤
      C * (gaussianFirstMoment n / Real.sqrt (2 * t) + gaussianSecondMoment n) := by
  let a := Real.sqrt (2 * t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  let K (z : V) := (innerSL ℝ z).smulRight (f (x + a • z))
  have hi := heatGradientKernel_integrable hf hbound t x
  have hmoment : Integrable (fun z : V => ‖z‖) (stdGaussian V) :=
    IsGaussian.integrable_id.norm
  have hsecond : Integrable (fun z : V => ‖z‖ ^ 2) (stdGaussian V) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian V)).integrable_norm_pow (by norm_num)
  have hmajor : Integrable (fun z : V => C * (‖z‖ + a * ‖z‖ ^ 2)) (stdGaussian V) :=
    (hmoment.add (hsecond.const_mul a)).const_mul C
  have hpoint (z : V) : (1 + ‖x‖) * ‖K z‖ ≤ C * (‖z‖ + a * ‖z‖ ^ 2) := by
    have hweight := radial_weight_translation x z ha.le
    have h := mul_le_mul_of_nonneg_right hweight (norm_nonneg (f (x + a • z)))
    have hb := mul_le_mul_of_nonneg_right (hbound (x + a • z))
      (show 0 ≤ 1 + a * ‖z‖ by positivity)
    have hfirst : (1 + ‖x‖) * ‖f (x + a • z)‖ ≤ C * (1 + a * ‖z‖) := by
      nlinarith [h, hb]
    have hprod := mul_le_mul_of_nonneg_left hfirst (norm_nonneg z)
    dsimp only [K]
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    nlinarith [hprod]
  have hnorm : (1 + ‖x‖) * ‖∫ z, K z ∂stdGaussian V‖ ≤
      C * (gaussianFirstMoment n + a * gaussianSecondMoment n) := by
    calc
      _ ≤ (1 + ‖x‖) * ∫ z, ‖K z‖ ∂stdGaussian V :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ = ∫ z, (1 + ‖x‖) * ‖K z‖ ∂stdGaussian V := (integral_const_mul _ _).symm
      _ ≤ ∫ z : V, C * (‖z‖ + a * ‖z‖ ^ 2) ∂stdGaussian V :=
        integral_mono (hi.norm.const_mul _) hmajor hpoint
      _ = C * (gaussianFirstMoment n + a * gaussianSecondMoment n) := by
        rw [integral_const_mul, integral_add hmoment (hsecond.const_mul a), integral_const_mul]
        rfl
  have h := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ha.le)
  change (1 + ‖x‖) * ‖a⁻¹ • ∫ z, K z ∂stdGaussian V‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ = a⁻¹ * ((1 + ‖x‖) * ‖∫ z, K z ∂stdGaussian V‖) := by ring
    _ ≤ a⁻¹ * (C * (gaussianFirstMoment n + a * gaussianSecondMoment n)) := h
    _ = C * (gaussianFirstMoment n / Real.sqrt (2 * t) + gaussianSecondMoment n) := by
      change _ = C * (gaussianFirstMoment n / a + gaussianSecondMoment n)
      field_simp [ha.ne']

end PoincareConjecture.M35.RadialGauge
