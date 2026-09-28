import PoincareConjecture.Proofs.M35.TerminalBlowup.RadialScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness


noncomputable def axisWarpingRadius (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  r * Real.sqrt (axisAngularCoefficient g r)


noncomputable def axisRadialSpeed (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  Real.sqrt (axisRadialCoefficient g r)



noncomputable def axisWarpingSlope (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  Real.sqrt (axisAngularCoefficient g r) * (1 + r ^ 2 * radialConnectionAlpha g r) /
    axisRadialSpeed g r



noncomputable def axisWarpingSecond (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  -axisWarpingRadius g r * radialMixedCurvatureFactor g r / axisRadialCoefficient g r


theorem axisAngularCoefficient_deriv_eq_connection
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    deriv (axisAngularCoefficient g) r =
      2 * axisAngularCoefficient g r * r * radialConnectionAlpha g r := by
  unfold radialConnectionAlpha
  field_simp [(axisAngularCoefficient_pos g r).ne', hr.ne']

private theorem correction_deriv
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    deriv (axisCorrectionCoefficient g) r =
      ((deriv (axisRadialCoefficient g) r - deriv (axisAngularCoefficient g) r) * r ^ 2 -
        2 * r * (axisRadialCoefficient g r - axisAngularCoefficient g r)) / (r ^ 2) ^ 2 := by
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hb := ((axisRadialCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hd := (hb.sub ha).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr.ne')
  convert! hd.deriv using 1
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one]
  ring


theorem axisRadialCoefficient_deriv_eq_connection
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    deriv (axisRadialCoefficient g) r =
      2 * axisRadialCoefficient g r * r *
        (2 * radialConnectionAlpha g r + radialConnectionBeta g r +
          radialConnectionGamma g r * r ^ 2) := by
  rw [radialConnectionGamma, correction_deriv g hr]
  unfold radialConnectionBeta radialConnectionAlpha axisCorrectionCoefficient
  field_simp [(axisAngularCoefficient_pos g r).ne',
    (axisRadialCoefficient_pos g r).ne', hr.ne']
  ring


theorem axisWarpingRadius_pos (g : RiemannianMetric 3 StandardCapSpace)
    {r : ℝ} (hr : 0 < r) : 0 < axisWarpingRadius g r :=
  mul_pos hr (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r))


theorem axisRadialSpeed_pos (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) :
    0 < axisRadialSpeed g r :=
  Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)



theorem axisWarpingRadius_hasDerivAt
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (axisWarpingRadius g)
      (axisRadialSpeed g r * axisWarpingSlope g r) r := by
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hs := ha.sqrt (axisAngularCoefficient_pos g r).ne'
  convert! (hasDerivAt_id r).mul hs using 1
  simp only [axisWarpingSlope, axisRadialSpeed, id_eq, one_mul]
  rw [axisAngularCoefficient_deriv_eq_connection g hr]
  have ha0 : Real.sqrt (axisAngularCoefficient g r) ≠ 0 :=
    (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne'
  have hb0 : Real.sqrt (axisRadialCoefficient g r) ≠ 0 :=
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne'
  field_simp [ha0, hb0]
  rw [Real.sq_sqrt (axisAngularCoefficient_pos g r).le]
  ring



theorem axisWarpingSlope_hasDerivAt
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (axisWarpingSlope g)
      (axisRadialSpeed g r * axisWarpingSecond g r) r := by
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hb := ((axisRadialCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hsa := ha.sqrt (axisAngularCoefficient_pos g r).ne'
  have hsb := hb.sqrt (axisRadialCoefficient_pos g r).ne'
  have hA := (((radialConnection_contDiffAt g hr).1).differentiableAt (by simp)).hasDerivAt
  have hk := (((hasDerivAt_id r).pow 2).mul hA).const_add 1
  have hd := (hsa.mul hk).div hsb
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne'
  convert! hd using 1
  simp only [axisRadialSpeed, axisWarpingSecond, axisWarpingRadius, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply, Pi.mul_apply]
  rw [axisAngularCoefficient_deriv_eq_connection g hr,
    axisRadialCoefficient_deriv_eq_connection g hr]
  have ha0 := (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne'
  have hb0 := (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne'
  unfold radialMixedCurvatureFactor
  field_simp [ha0, hb0, (axisRadialCoefficient_pos g r).ne']
  ring_nf
  simp only [Real.sq_sqrt (axisAngularCoefficient_pos g r).le,
    Real.sq_sqrt (axisRadialCoefficient_pos g r).le,
    show Real.sqrt (axisRadialCoefficient g r) ^ 4 = axisRadialCoefficient g r ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
        Real.sq_sqrt (axisRadialCoefficient_pos g r).le]]
  ring



theorem radialTangentialCurvatureFactor_eq_warping
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    radialTangentialCurvatureFactor g r / axisAngularCoefficient g r =
      (1 - axisWarpingSlope g r ^ 2) / axisWarpingRadius g r ^ 2 := by
  unfold radialTangentialCurvatureFactor axisWarpingSlope axisWarpingRadius axisRadialSpeed
    radialConnectionBeta radialConnectionAlpha axisCorrectionCoefficient
  have ha0 := (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne'
  have hb0 := (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne'
  field_simp [ha0, hb0, (axisAngularCoefficient_pos g r).ne',
    (axisRadialCoefficient_pos g r).ne', hr.ne']
  simp only [Real.sq_sqrt (axisAngularCoefficient_pos g r).le,
    Real.sq_sqrt (axisRadialCoefficient_pos g r).le]
  ring



theorem radialMixedCurvatureFactor_eq_warping
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    radialMixedCurvatureFactor g r / axisRadialCoefficient g r =
      -axisWarpingSecond g r / axisWarpingRadius g r := by
  unfold axisWarpingSecond
  field_simp [(axisWarpingRadius_pos g hr).ne']

end PoincareConjecture.M35.Uniqueness
