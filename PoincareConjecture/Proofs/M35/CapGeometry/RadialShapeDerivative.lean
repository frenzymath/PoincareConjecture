import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

theorem radial_shape_hasDerivAt
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => axisWarpingSlope g s / axisWarpingRadius g s)
      (-axisRadialSpeed g r * (radialMixedCurvatureFactor g r / axisRadialCoefficient g r +
        (axisWarpingSlope g r / axisWarpingRadius g r) ^ 2)) r := by
  have h := (axisWarpingSlope_hasDerivAt g hr).div (axisWarpingRadius_hasDerivAt g hr)
    (axisWarpingRadius_pos g hr).ne'
  convert! h using 1
  unfold axisWarpingSecond
  field_simp [(axisWarpingRadius_pos g hr).ne', (axisRadialCoefficient_pos g r).ne']
  ring

theorem radialUnitField_inner
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (w : StandardCapSpace) :
    g.inner x (radialUnitField g x) w =
      axisRadialSpeed g ‖x‖ / ‖x‖ * inner ℝ x w := by
  simp only [radialUnitField, map_smul, smul_apply, smul_eq_mul]
  rw [rotational_inner_position g hrotation hx]
  unfold axisRadialSpeed
  field_simp [norm_ne_zero_iff.mpr hx,
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g ‖x‖)).ne']
  rw [Real.sq_sqrt (axisRadialCoefficient_pos g ‖x‖).le]

private theorem radius_hasFDerivAt {x : StandardCapSpace} (hx : x ≠ 0) :
    HasFDerivAt (fun y : StandardCapSpace => ‖y‖)
      (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  convert! h using 1
  ext w
  simp [smul_eq_mul]
  ring

theorem radial_shape_hasFDerivAt
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    HasFDerivAt (fun y => axisWarpingSlope g ‖y‖ / axisWarpingRadius g ‖y‖)
      (-(radialMixedCurvatureFactor g ‖x‖ / axisRadialCoefficient g ‖x‖ +
        (axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖) ^ 2) •
          g.euclideanCoefficients x (radialUnitField g x)) x := by
  have h := (radial_shape_hasDerivAt g (norm_pos_iff.mpr hx)).comp_hasFDerivAt x
    (radius_hasFDerivAt hx)
  convert! h using 1
  ext w
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  change -(radialMixedCurvatureFactor g ‖x‖ / axisRadialCoefficient g ‖x‖ +
      (axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖) ^ 2) *
        g.inner x (radialUnitField g x) w = _
  rw [radialUnitField_inner g hrotation hx]
  ring

end PoincareConjecture.M35.Uniqueness
