import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope
import PoincareConjecture.Proofs.M13.OrdinaryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem axisWarpingRadius_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    axisWarpingRadius (M13.scaleSmoothMetric g Q hQ) r =
      Real.sqrt Q * axisWarpingRadius g r := by
  unfold axisWarpingRadius axisAngularCoefficient
  rw [M13.scaleSmoothMetric_inner, Real.sqrt_mul hQ.le]
  ring

theorem axisRadialSpeed_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    axisRadialSpeed (M13.scaleSmoothMetric g Q hQ) r =
      Real.sqrt Q * axisRadialSpeed g r := by
  unfold axisRadialSpeed axisRadialCoefficient
  rw [M13.scaleSmoothMetric_inner, Real.sqrt_mul hQ.le]

theorem axisWarpingSlope_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) {r : ℝ} (hr : 0 < r) :
    axisWarpingSlope (M13.scaleSmoothMetric g Q hQ) r = axisWarpingSlope g r := by
  have hscaled := axisWarpingRadius_hasDerivAt (M13.scaleSmoothMetric g Q hQ) hr
  have heq : axisWarpingRadius (M13.scaleSmoothMetric g Q hQ) =
      fun s => Real.sqrt Q * axisWarpingRadius g s :=
    funext (axisWarpingRadius_scale g Q hQ)
  rw [heq] at hscaled
  have h := hscaled.unique ((axisWarpingRadius_hasDerivAt g hr).const_mul (Real.sqrt Q))
  rw [axisRadialSpeed_scale] at h
  have hfactor : Real.sqrt Q * axisRadialSpeed g r ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr hQ).ne' (axisRadialSpeed_pos g r).ne'
  apply mul_left_cancel₀ hfactor
  simpa only [mul_assoc] using h

theorem axisWarpingSecond_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) {r : ℝ} (hr : 0 < r) :
    axisWarpingSecond (M13.scaleSmoothMetric g Q hQ) r =
      axisWarpingSecond g r / Real.sqrt Q := by
  have heq : axisWarpingSlope (M13.scaleSmoothMetric g Q hQ) =ᶠ[𝓝 r]
      axisWarpingSlope g := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact axisWarpingSlope_scale g Q hQ hs
  have hscaled := (axisWarpingSlope_hasDerivAt
    (M13.scaleSmoothMetric g Q hQ) hr).congr_of_eventuallyEq heq.symm
  have h := hscaled.unique (axisWarpingSlope_hasDerivAt g hr)
  rw [axisRadialSpeed_scale] at h
  apply (eq_div_iff (Real.sqrt_pos.mpr hQ).ne').mpr
  have hspeed := (axisRadialSpeed_pos g r).ne'
  apply mul_left_cancel₀ hspeed
  nlinarith only [h]

theorem radialMixedSectional_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) {r : ℝ} (hr : 0 < r) :
    radialMixedCurvatureFactor (M13.scaleSmoothMetric g Q hQ) r /
        axisRadialCoefficient (M13.scaleSmoothMetric g Q hQ) r =
      (radialMixedCurvatureFactor g r / axisRadialCoefficient g r) / Q := by
  rw [radialMixedCurvatureFactor_eq_warping _ hr,
    radialMixedCurvatureFactor_eq_warping g hr, axisWarpingSecond_scale _ _ _ hr,
    axisWarpingRadius_scale]
  have hsqrt := (Real.sqrt_pos.mpr hQ).ne'
  have hradius := (axisWarpingRadius_pos g hr).ne'
  field_simp [hsqrt, hradius, hQ.ne']
  rw [Real.sq_sqrt hQ.le]

end PoincareConjecture.M35.Uniqueness
