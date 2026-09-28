import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointLift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_lifted_boundary_length_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {gamma : ℝ → AnnulusCoordinates}
    {J : Set ℝ} (hJ : IsOpen J) (hg : ContDiffOn ℝ ∞ gamma J)
    (he : ∀ s ∈ J, DifferentiableAt ℝ e (gamma s))
    (hlift : ∀ s ∈ J, e (gamma s) = intrinsicAnnulusBoundary 2 s)
    {a b c : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J) (hc : 0 ≤ c)
    (hbound : ∀ s ∈ Icc a b, ∀ v : AnnulusCoordinates,
      c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 (gamma s 0)) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e (gamma s)) (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    c * |intrinsicBoundaryLength N.metric 1 (gamma a 0) (gamma b 0)| ≤
      intrinsicBoundaryLength N.metric 2 a b := by
  let f : ℝ → ℝ := fun s => gamma s 0
  let f' : ℝ → ℝ := fun s => deriv gamma s 0
  have hga (s : ℝ) (hs : s ∈ Icc a b) : ContDiffAt ℝ ∞ gamma s :=
    hg.contDiffAt (hJ.mem_nhds (hsub hs))
  have hdf (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt f (f' s) s :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (gamma s) 0).comp_hasDerivAt s
      ((hga s hs).differentiableAt (by simp)).hasDerivAt
  have hf : ContinuousOn f (Icc a b) := fun s hs => (hdf s hs).continuousAt.continuousWithinAt
  have hf' : ContinuousOn f' (Icc a b) := by
    intro s hs
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.comp
      ((hga s hs).derivWithin (m := 0) (by simp)).continuousAt).continuousWithinAt
  have hspeed := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have houter := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (2 : ℝ) ≠ 0)).continuous
  have hsubst : (∫ s in a..b, intrinsicBoundarySpeed N.metric 1 (f s) * f' s) =
      intrinsicBoundaryLength N.metric 1 (gamma a 0) (gamma b 0) := by
    change (∫ s in a..b, (intrinsicBoundarySpeed N.metric 1 ∘ f) s * f' s) =
      ∫ s in f a..f b, intrinsicBoundarySpeed N.metric 1 s
    apply intervalIntegral.integral_comp_mul_deriv
    · simpa only [uIcc_of_le hab] using hdf
    · simpa only [uIcc_of_le hab] using hf'
    · exact hspeed
  have hcontinuous : ContinuousOn (fun s => c * intrinsicBoundarySpeed N.metric 1 (f s) * f' s)
      (Icc a b) := (continuousOn_const.mul (hspeed.comp_continuousOn hf)).mul hf'
  have hscaled : (∫ s in a..b, c * intrinsicBoundarySpeed N.metric 1 (f s) * f' s) =
      c * intrinsicBoundaryLength N.metric 1 (gamma a 0) (gamma b 0) := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, hsubst]
  calc
    _ = |c * intrinsicBoundaryLength N.metric 1 (gamma a 0) (gamma b 0)| := by
      rw [abs_mul, abs_of_nonneg hc]
    _ = |∫ s in a..b, c * intrinsicBoundarySpeed N.metric 1 (f s) * f' s| :=
      congrArg abs hscaled.symm
    _ ≤ ∫ s in a..b, |c * intrinsicBoundarySpeed N.metric 1 (f s) * f' s| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ intrinsicBoundaryLength N.metric 2 a b := by
      apply intervalIntegral.integral_mono_on hab
        (hcontinuous.abs.intervalIntegrable_of_Icc hab) (houter.intervalIntegrable a b)
      intro s hs
      rw [abs_mul, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg (show 0 ≤ intrinsicBoundarySpeed N.metric 1 (f s) from Real.sqrt_nonneg _)]
      apply m64Intrinsic_boundary_lift_speed_le N (he s (hsub hs))
        ((hga s hs).differentiableAt (by simp)) _ (hbound s hs)
      filter_upwards [hJ.mem_nhds (hsub hs)] with x hx
      exact hlift x hx

end PoincareConjecture
