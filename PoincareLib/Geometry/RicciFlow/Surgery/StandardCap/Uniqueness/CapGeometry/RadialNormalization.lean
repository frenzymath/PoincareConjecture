import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.RadialEndSlope
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction

/-!
# Actual radial quantities under scalar normalization

Constant metric scaling multiplies actual radial arclength and orbit radius
by the square root of the scale.  Differentiating the already proved radius
identities shows that the intrinsic slope is unchanged and that the second
derivative and mixed sectional factor have their geometric scaling laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

/-- Actual orbit radius has the square-root metric scaling law. -/
theorem axisWarpingRadius_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    axisWarpingRadius (M13.scaleSmoothMetric g Q hQ) r =
      Real.sqrt Q * axisWarpingRadius g r := by
  unfold axisWarpingRadius axisAngularCoefficient
  rw [M13.scaleSmoothMetric_inner, Real.sqrt_mul hQ.le]
  ring

/-- The actual original-coordinate radial speed has the same square-root
metric scaling law. -/
theorem axisRadialSpeed_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    axisRadialSpeed (M13.scaleSmoothMetric g Q hQ) r =
      Real.sqrt Q * axisRadialSpeed g r := by
  unfold axisRadialSpeed axisRadialCoefficient
  rw [M13.scaleSmoothMetric_inner, Real.sqrt_mul hQ.le]

/-- The actual intrinsic orbit slope is unchanged by scalar metric
normalization. -/
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

/-- The actual intrinsic orbit-radius second derivative scales by the
inverse square root of the metric factor. -/
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

/-- The actual mixed sectional factor scales by the inverse scalar
normalization factor. -/
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

end PoincareMT.M35.Uniqueness
