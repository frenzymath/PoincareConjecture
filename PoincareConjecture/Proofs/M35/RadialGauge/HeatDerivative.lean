import PoincareConjecture.Proofs.M35.RadialGauge.GaussianEuclidean
import PoincareConjecture.Proofs.M35.RadialGauge.HeatGradient
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem heatAverage_hasFDerivAt_integral {f : V → F} {f' : V → V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hdbound : ∀ x, ‖f' x‖ ≤ D) (t : ℝ) (x : V) :
    HasFDerivAt (heatAverage t f)
      (∫ z, f' (x + Real.sqrt (2 * t) • z) ∂stdGaussian V) x := by
  change HasFDerivAt (fun y => ∫ z, f (y + Real.sqrt (2 * t) • z) ∂stdGaussian V) _ x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := univ) (F' := fun y z => f' (y + Real.sqrt (2 * t) • z))
    (bound := fun _ => D) (by simp)
  · exact Eventually.of_forall (fun y => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact heatAverage_integrable hf hbound t x
  · exact (hf'.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z y _ => hdbound _)
  · exact integrable_const D
  · refine Eventually.of_forall (fun z y _ => ?_)
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (hderiv _).comp y ((hasFDerivAt_id y).add_const (Real.sqrt (2 * t) • z))

theorem heatAverage_derivative_integral_eq_kernel {f : V → F}
    {f' : V → V →L[ℝ] F} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hdbound : ∀ x, ‖f' x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : V) :
    (∫ z, f' (x + Real.sqrt (2 * t) • z) ∂stdGaussian V) =
      heatGradientKernel t f x := by
  let a := Real.sqrt (2 * t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hc : Continuous (fun z : V => x + a • z) := by fun_prop
  have hi : Integrable (fun z : V => f' (x + a • z)) (stdGaussian V) :=
    (integrable_const D).mono' (hf'.comp hc).aestronglyMeasurable
      (Eventually.of_forall (fun z => hdbound _))
  have hk := heatGradientKernel_integrable hf hbound t x
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
  have hb (z : V) : ‖f (x + a • z)‖ ≤ C := by
    nlinarith [hbound (x + a • z),
      mul_nonneg (norm_nonneg (x + a • z)) (norm_nonneg (f (x + a • z)))]
  have hdb (z : V) : ‖a • f' (x + a • z)‖ ≤ a * D := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hdbound _) ha.le
  have hparts := integral_stdGaussian_coordinate_derivative i (hf.comp hc)
    ((hf'.comp hc).const_smul a) hd hb hdb
  simp only [Function.comp_def, Pi.smul_apply, smul_apply, integral_smul] at hparts
  have hid : (∫ z, f' (x + a • z) (EuclideanSpace.single i (1 : ℝ)) ∂stdGaussian V) =
      a⁻¹ • ∫ z : V, z i • f (x + a • z) ∂stdGaussian V := by
    rw [← hparts, inv_smul_smul₀ ha.ne']
  rw [ContinuousLinearMap.integral_apply hi, heatGradientKernel,
    smul_apply, ContinuousLinearMap.integral_apply hk]
  simpa only [a, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hid

theorem heatAverage_hasFDerivAt {f : V → F} {f' : V → V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hdbound : ∀ x, ‖f' x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : V) :
    HasFDerivAt (heatAverage t f) (heatGradientKernel t f x) x := by
  rw [← heatAverage_derivative_integral_eq_kernel hf hf' hderiv hbound hdbound ht x]
  exact heatAverage_hasFDerivAt_integral hf hf' hderiv hbound hdbound t x

theorem heatAverage_fderiv_weighted_norm_le {f : V → F} {f' : V → V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (hdbound : ∀ x, ‖f' x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : V) :
    (1 + ‖x‖) * ‖fderiv ℝ (heatAverage t f) x‖ ≤
      C * (gaussianFirstMoment (n + 1) / Real.sqrt (2 * t) + gaussianSecondMoment (n + 1)) := by
  rw [(heatAverage_hasFDerivAt hf hf' hderiv hbound hdbound ht x).fderiv]
  exact heatGradientKernel_weighted_norm_le hf hbound ht x

end PoincareConjecture.M35.RadialGauge
