import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional










set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology Convolution ContDiff

namespace PoincareConjecture.M60




noncomputable def cauchyTransformKernel : ℂ → ℂ :=
  (ball (0 : ℂ) 3).indicator (fun z => (Real.pi⁻¹ : ℝ) • z⁻¹)




theorem integrable_cauchyTransformKernel : Integrable cauchyTransformKernel := by
  have hi : IntegrableOn (fun z : ℂ => z⁻¹) (ball 0 3) := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)
      (by norm_num [Complex.finrank_real_complex])
      (by norm_num [Complex.finrank_real_complex])
    · exact Eventually.of_forall (fun z => by simp [Real.rpow_neg_one])
    · exact measurable_inv.aestronglyMeasurable
  exact (integrable_indicator_iff measurableSet_ball).2 (hi.smul (Real.pi⁻¹ : ℝ))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]



noncomputable def cauchyTransform (f : ℂ → V) : ℂ → V :=
  cauchyTransformKernel ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] f




theorem contDiff_cauchyTransform {k : ℕ∞} {f : ℂ → V}
    (hf : ContDiff ℝ k f) (hc : HasCompactSupport f) :
    ContDiff ℝ k (cauchyTransform f) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    integrable_cauchyTransformKernel.locallyIntegrable hf



theorem norm_cauchyTransform_le {f : ℂ → V} {B : ℝ}
    (hB : ∀ z, ‖f z‖ ≤ B) (z : ℂ) :
    ‖cauchyTransform f z‖ ≤ (∫ w : ℂ, ‖cauchyTransformKernel w‖) * B := by
  change ‖∫ w : ℂ, cauchyTransformKernel w • f (z - w)‖ ≤ _
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (integrable_cauchyTransformKernel.norm.mul_const B)
  exact Eventually.of_forall fun w => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB (z - w)) (norm_nonneg _)




theorem fderiv_cauchyTransform_apply {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (z d : ℂ) :
    fderiv ℝ (cauchyTransform f) z d =
      cauchyTransform (fun w => fderiv ℝ f w d) z := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    integrable_cauchyTransformKernel.locallyIntegrable hf z
  rw [show fderiv ℝ (cauchyTransform f) z = _ from hd.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℂ)
    integrable_cauchyTransformKernel.locallyIntegrable (hc.fderiv ℝ)
    (hf.continuous_fderiv (by simp)) z d

end PoincareConjecture.M60
