import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformPrimitive

set_option autoImplicit false

open Complex Set MeasureTheory Metric
open scoped Topology ContDiff Convolution

namespace PoincareConjecture.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in

theorem cauchyRiemannDerivative_cauchyTransform {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (z : ℂ) :
    cauchyRiemannDerivative (cauchyTransform f) z =
      cauchyTransform (cauchyRiemannDerivative f) z := by
  have hi (d : ℂ) : Integrable (fun w : ℂ =>
      cauchyTransformKernel w • fderiv ℝ f (z - w) d) :=
    (hc.fderiv_apply ℝ d).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
      integrable_cauchyTransformKernel.locallyIntegrable
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) z
  unfold cauchyRiemannDerivative
  rw [fderiv_cauchyTransform_apply hf hc, fderiv_cauchyTransform_apply hf hc]
  change (1 / 2 : ℝ) • ((∫ w : ℂ, cauchyTransformKernel w •
      fderiv ℝ f (z - w) 1) + I •
      (∫ w : ℂ, cauchyTransformKernel w • fderiv ℝ f (z - w) I)) =
    ∫ w : ℂ, cauchyTransformKernel w • ((1 / 2 : ℝ) •
      (fderiv ℝ f (z - w) 1 + I • fderiv ℝ f (z - w) I))
  simp_rw [smul_comm (cauchyTransformKernel _) (1 / 2 : ℝ), smul_add,
    smul_comm (cauchyTransformKernel _) I]
  have h1 : Integrable (fun w : ℂ => (1 / 2 : ℝ) •
      cauchyTransformKernel w • fderiv ℝ f (z - w) 1) := (hi 1).smul _
  have h2 : Integrable (fun w : ℂ => (1 / 2 : ℝ) • I •
      cauchyTransformKernel w • fderiv ℝ f (z - w) I) := ((hi I).smul I).smul _
  rw [integral_add h1 h2]
  simp only [integral_smul]

theorem cauchyTransform_rightInverse {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ closedBall (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    cauchyRiemannDerivative (cauchyTransform f) z = f z := by
  rw [cauchyRiemannDerivative_cauchyTransform hf hc,
    cauchyTransform_cauchyRiemannDerivative hf]
  have hzero (θ : ℝ) : f (z - circleMap 0 3 θ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hb := hs ht
    rw [mem_closedBall_zero_iff] at hb
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hn := norm_sub_le z (z - circleMap 0 3 θ)
    have he : z - (z - circleMap 0 3 θ) = circleMap 0 3 θ := by abel
    rw [he, norm_circleMap_zero] at hn
    norm_num at hn
    linarith
  simp_rw [hzero, zero_sub]
  rw [intervalIntegral.integral_const, smul_smul]
  have hp : -(1 / (2 * Real.pi)) * (Real.pi - -Real.pi) = (-1 : ℝ) := by
    field_simp
    ring
  rw [hp, neg_one_smul, neg_neg]

end PoincareConjecture.M60
