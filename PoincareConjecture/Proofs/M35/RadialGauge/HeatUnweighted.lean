import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.HeatSmoothness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem heatGradientKernel_integrable_of_bound {f : V → F}
    (hf : Continuous f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (t : ℝ) (x : V) :
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
  exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)

theorem heatGradientKernel_norm_le {f : V → F} (hf : Continuous f)
    {C t : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (ht : 0 < t) (x : V) :
    ‖heatGradientKernel t f x‖ ≤ C * gaussianFirstMoment (n + 1) / Real.sqrt (2 * t) := by
  have hi := heatGradientKernel_integrable_of_bound hf hbound t x
  have hmoment : Integrable (fun z : V => ‖z‖) (stdGaussian V) :=
    IsGaussian.integrable_id.norm
  have ha : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  rw [heatGradientKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (Real.sqrt (2 * t))⁻¹ * ∫ z : V, ‖z‖ * C ∂stdGaussian V := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      apply (norm_integral_le_integral_norm _).trans
      apply integral_mono hi.norm (hmoment.mul_const C)
      intro z
      dsimp only
      rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = _ := by
      rw [integral_mul_const]
      rw [div_eq_mul_inv, gaussianFirstMoment]
      ring

theorem heatAverage_derivative_eq_kernel_of_bounds {f : V → F}
    {f' : V → V →L[ℝ] F} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖f' x‖ ≤ D)
    {t : ℝ} (ht : 0 < t) (x : V) :
    heatAverage t f' x = heatGradientKernel t f x := by
  let a := Real.sqrt (2 * t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hc : Continuous (fun z : V => x + a • z) := by fun_prop
  have hi := heatAverage_integrable_of_bound hf' hdbound t x
  have hk := heatGradientKernel_integrable_of_bound hf hbound t x
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (∫ z, f' (x + a • z) ∂stdGaussian V) (EuclideanSpace.single i (1 : ℝ)) =
    heatGradientKernel t f x (EuclideanSpace.single i (1 : ℝ))
  have hd : ∀ z, HasFDerivAt (fun w : V => f (x + a • w))
      (a • f' (x + a • z)) z := by
    intro z
    simpa only [Function.comp_def, Pi.smul_apply, id_eq,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
      (hderiv _).comp z (((hasFDerivAt_id z).const_smul a).const_add x)
  have hdb (z : V) : ‖a • f' (x + a • z)‖ ≤ a * D := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hdbound _) ha.le
  have hparts := integral_stdGaussian_coordinate_derivative i (hf.comp hc)
    ((hf'.comp hc).const_smul a) hd (fun z => hbound (x + a • z)) hdb
  simp only [Function.comp_def, Pi.smul_apply, smul_apply, integral_smul] at hparts
  have hid : (∫ z, f' (x + a • z) (EuclideanSpace.single i (1 : ℝ)) ∂stdGaussian V) =
      a⁻¹ • ∫ z : V, z i • f (x + a • z) ∂stdGaussian V := by
    rw [← hparts, inv_smul_smul₀ ha.ne']
  rw [ContinuousLinearMap.integral_apply hi, heatGradientKernel,
    smul_apply, ContinuousLinearMap.integral_apply hk]
  simpa only [a, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hid

theorem heatAverage_hasFDerivAt_kernel_of_bounds {f : V → F}
    {f' : V → V →L[ℝ] F} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖f' x‖ ≤ D)
    {t : ℝ} (ht : 0 < t) (x : V) :
    HasFDerivAt (heatAverage t f) (heatGradientKernel t f x) x := by
  rw [← heatAverage_derivative_eq_kernel_of_bounds hf hf' hderiv hbound hdbound ht x]
  exact heatAverage_hasFDerivAt_of_bounds hf hf' hderiv hbound hdbound t x

theorem heatGradientKernel_norm_le_rpow {f : V → F} (hf : Continuous f)
    {C t : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) (ht : 0 < t) (x : V) :
    ‖heatGradientKernel t f x‖ ≤ C * gaussianFirstMoment (n + 1) * t ^ (-(1 / 2 : ℝ)) := by
  apply (heatGradientKernel_norm_le hf hbound ht x).trans
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC gaussianFirstMoment_nonneg)
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  apply (inv_le_inv₀ (by positivity) (Real.sqrt_pos.mpr ht)).mpr
  exact Real.sqrt_le_sqrt (by linarith)

theorem heatDuhamelGradient_norm_le {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, ‖f s x‖ ≤ C) (x : V) :
    ‖heatDuhamelGradient f t x‖ ≤ C * (2 * gaussianFirstMoment (n + 1) * Real.sqrt t) := by
  let B (s : ℝ) := C * gaussianFirstMoment (n + 1) * (t - s) ^ (-(1 / 2 : ℝ))
  have hB : IntervalIntegrable B volume 0 t :=
    (intervalIntegrable_backwards_invSqrt t).const_mul _
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖heatGradientKernel (t - s) (f s) x‖ ≤ B s := by
    by_cases hst : s < t
    · exact heatGradientKernel_norm_le_rpow (hf s ⟨hs.1.le, hs.2⟩)
        hC (hbound s ⟨hs.1.le, hs.2⟩) (sub_pos.mpr hst) x
    · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp only [heatGradientKernel, sub_self, mul_zero, Real.sqrt_zero, inv_zero,
        zero_smul, norm_zero]
      exact mul_nonneg (mul_nonneg hC gaussianFirstMoment_nonneg)
        (Real.rpow_nonneg (by simp) _)
  have h := intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall hb) hB
  change ‖heatDuhamelGradient f t x‖ ≤ ∫ s in (0 : ℝ)..t, B s at h
  convert! h using 1
  dsimp only [B]
  rw [intervalIntegral.integral_const_mul, integral_backwards_invSqrt]
  ring

theorem heatDuhamel_hasFDerivAt_of_bounds {f : ℝ → V → F}
    {f' : ℝ → V → V →L[ℝ] F} {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hf' : ∀ s ∈ Ico 0 t, Continuous (f' s))
    (hderiv : ∀ s ∈ Ico 0 t, ∀ x, HasFDerivAt (f s) (f' s x) x)
    (hdbound : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x, ‖f' s x‖ ≤ D)
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, ‖f s x‖ ≤ C) (x : V) :
    HasFDerivAt (heatDuhamel f t) (heatDuhamelGradient f t x) x := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc 0 t)) := by
    rw [uIoc_of_le ht]
    infer_instance
  let B (s : ℝ) := C * gaussianFirstMoment (n + 1) * (t - s) ^ (-(1 / 2 : ℝ))
  have hB : IntervalIntegrable B volume 0 t :=
    (intervalIntegrable_backwards_invSqrt t).const_mul _
  have hs : ∀ᵐ s ∂volume.restrict (uIoc 0 t), s ∈ Ico 0 t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc 0 t)).ae_ne t] with s hs hne
    rw [uIoc_of_le ht] at hs
    exact ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
  unfold heatDuhamel heatDuhamelGradient
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := univ) (F' := fun y s => heatGradientKernel (t - s) (f s) y)
    (bound := B) (by simp)
  · exact Eventually.of_forall (fun y =>
      (heatAverage_time_stronglyMeasurable hfm t y).aestronglyMeasurable)
  · rw [intervalIntegrable_iff]
    apply (integrable_const C).mono'
      (heatAverage_time_stronglyMeasurable hfm t x).aestronglyMeasurable
    filter_upwards [hs] with s hs
    exact heatAverage_norm_le (hf s ⟨hs.1, hs.2.le⟩)
      (hbound s ⟨hs.1, hs.2.le⟩) (t - s) x
  · exact (heatGradientKernel_time_stronglyMeasurable hfm t x).aestronglyMeasurable
  · filter_upwards [hs] with s hs y _
    exact heatGradientKernel_norm_le_rpow (hf s ⟨hs.1, hs.2.le⟩)
      hC (hbound s ⟨hs.1, hs.2.le⟩) (sub_pos.mpr hs.2) y
  · exact hB
  · filter_upwards [hs] with s hs y _
    obtain ⟨D, hD⟩ := hdbound s hs
    exact heatAverage_hasFDerivAt_kernel_of_bounds (hf s ⟨hs.1, hs.2.le⟩)
      (hf' s hs) (hderiv s hs) (hbound s ⟨hs.1, hs.2.le⟩) hD (sub_pos.mpr hs.2) y

end PoincareConjecture.M35.RadialGauge
