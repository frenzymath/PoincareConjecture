import PoincareConjecture.Proofs.M60.Mathlib.HolomorphicFrameSeries
import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformRightInverse










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M60

section Projection

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]



noncomputable def cauchyRiemannProjection : (ℂ →L[ℝ] W) →L[ℝ] W :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ W (1 : ℂ) +
    Complex.I • ContinuousLinearMap.apply ℝ W Complex.I)



theorem cauchyRiemannProjection_fderiv (f : ℂ → W) (z : ℂ) :
    cauchyRiemannProjection (fderiv ℝ f z) = cauchyRiemannDerivative f z := rfl

end Projection

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [CompleteSpace V]




theorem cauchyRiemannDerivative_holomorphicFrameSum
    {A : ℂ → V →L[ℂ] V} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) (z : ℂ) :
    cauchyRiemannDerivative (holomorphicFrameSum A) z =
      ∑' j, cauchyRiemannDerivative (holomorphicFrameTerm A j) z := by
  rw [← cauchyRiemannProjection_fderiv,
    (hasFDerivAt_holomorphicFrameSum hA hc ha hq hq1 hsmall hAb hDAb z).fderiv]
  exact cauchyRiemannProjection.map_tsum
    (summable_holomorphicFrameTerm hA hc ha hq hq1 hsmall hAb hDAb z).2



theorem cauchyRiemannDerivative_holomorphicFrameSum_eq_mul
    {A : ℂ → V →L[ℂ] V} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    (hs : tsupport A ⊆ closedBall (0 : ℂ) 1)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    cauchyRiemannDerivative (holomorphicFrameSum A) z = A z * holomorphicFrameSum A z := by
  have hsum := summable_holomorphicFrameTerm hA hc ha hq hq1 hsmall hAb hDAb z
  have hcr : Summable (fun j => cauchyRiemannDerivative (holomorphicFrameTerm A j) z) :=
    cauchyRiemannProjection.summable hsum.2
  rw [cauchyRiemannDerivative_holomorphicFrameSum hA hc ha hq hq1 hsmall hAb hDAb,
    hcr.tsum_eq_zero_add]
  have hzero : cauchyRiemannDerivative (holomorphicFrameTerm A 0) z = 0 := by
    simp [holomorphicFrameTerm, cauchyRiemannDerivative, fderiv_const_apply]
  rw [hzero, zero_add]
  calc
    (∑' j, cauchyRiemannDerivative (holomorphicFrameTerm A (j + 1)) z) =
        ∑' j, A z * holomorphicFrameTerm A j z := by
      apply tsum_congr
      intro j
      exact cauchyTransform_rightInverse
        (contDiff_operator_mul hA (contDiff_holomorphicFrameTerm hA hc j)) hc.mul_right
        (tsupport_mul_subset_left.trans hs) hz
    _ = A z * holomorphicFrameSum A z :=
      ((ContinuousLinearMap.mul ℂ (V →L[ℂ] V) (A z)).map_tsum hsum.1).symm




theorem exists_c1_invertible_frame_of_smallCoefficient
    {A : ℂ → V →L[ℂ] V} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    (hs : tsupport A ⊆ closedBall (0 : ℂ) 1)
    {a : ℝ} (ha : 0 ≤ a) (hsmall : 2 * cauchyKernelNorm * a ≤ 1 / 4)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) :
    ∃ P : ℂ → V →L[ℂ] V, ContDiff ℝ 1 P ∧ (∀ z, IsUnit (P z)) ∧
      ∀ z ∈ ball (0 : ℂ) 1, cauchyRiemannDerivative P z = (A z).comp (P z) := by
  refine ⟨holomorphicFrameSum A,
    contDiff_holomorphicFrameSum hA hc ha (by norm_num) (by norm_num) hsmall hAb hDAb,
    isUnit_holomorphicFrameSum hA hc ha hsmall hAb hDAb, ?_⟩
  intro z hz
  exact cauchyRiemannDerivative_holomorphicFrameSum_eq_mul hA hc hs ha
    (by norm_num) (by norm_num) hsmall hAb hDAb hz

end PoincareConjecture.M60
