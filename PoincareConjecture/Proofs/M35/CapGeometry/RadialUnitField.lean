import PoincareConjecture.Proofs.M35.CapGeometry.RadialNormalization










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness


noncomputable def radialUnitField (g : RiemannianMetric 3 StandardCapSpace)
    (x : StandardCapSpace) : StandardCapSpace :=
  (‖x‖ * axisRadialSpeed g ‖x‖)⁻¹ • x

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

private theorem amplitude_hasDerivAt (g : RiemannianMetric 3 StandardCapSpace)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => (s * axisRadialSpeed g s)⁻¹)
      (-(1 + r ^ 2 * (2 * radialConnectionAlpha g r +
        radialConnectionBeta g r + radialConnectionGamma g r * r ^ 2)) /
          (r ^ 2 * axisRadialSpeed g r)) r := by
  have hb := ((axisRadialCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hs := hb.sqrt (axisRadialCoefficient_pos g r).ne'
  have hd := ((hasDerivAt_id r).mul hs).inv
    (mul_ne_zero hr.ne' (axisRadialSpeed_pos g r).ne')
  convert! hd using 1
  simp only [Pi.mul_apply, id_eq, one_mul]
  rw [axisRadialCoefficient_deriv_eq_connection g hr]
  unfold axisRadialSpeed
  field_simp [hr.ne', (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne']
  rw [Real.sq_sqrt (axisRadialCoefficient_pos g r).le]
  ring


theorem radialUnitField_contDiffAt (g : RiemannianMetric 3 StandardCapSpace)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radialUnitField g) x := by
  have hr : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
  have hb := (axisRadialCoefficient_contDiff g).contDiffAt.comp x hr
  have hs := hb.sqrt (axisRadialCoefficient_pos g ‖x‖).ne'
  exact ((hr.mul hs).inv (mul_ne_zero (norm_ne_zero_iff.mpr hx)
    (axisRadialSpeed_pos g ‖x‖).ne')).smul contDiffAt_id



theorem rotational_inner_position
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (w : StandardCapSpace) :
    g.inner x x w = axisRadialCoefficient g ‖x‖ * inner ℝ x w := by
  rw [rotational_metric_form_correction g hrotation hx]
  simp only [real_inner_self_eq_norm_sq, axisCorrectionCoefficient]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring


theorem radialUnitField_unit
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    g.inner x (radialUnitField g x) (radialUnitField g x) = 1 := by
  simp only [radialUnitField, map_smul, smul_apply, smul_eq_mul]
  rw [rotational_inner_position g hrotation hx, real_inner_self_eq_norm_sq]
  unfold axisRadialSpeed
  field_simp [norm_ne_zero_iff.mpr hx,
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g ‖x‖)).ne']
  rw [Real.sq_sqrt (axisRadialCoefficient_pos g ‖x‖).le]



theorem radialUnitField_projection
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (w : StandardCapSpace) :
    g.inner x (radialUnitField g x) w • radialUnitField g x =
      (inner ℝ x w / ‖x‖ ^ 2) • x := by
  simp only [radialUnitField, map_smul, smul_apply, smul_eq_mul, smul_smul]
  rw [rotational_inner_position g hrotation hx]
  congr 1
  unfold axisRadialSpeed
  field_simp [norm_ne_zero_iff.mpr hx,
    (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g ‖x‖)).ne']
  rw [Real.sq_sqrt (axisRadialCoefficient_pos g ‖x‖).le]



theorem radialUnitField_connection
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (w : StandardCapSpace) :
    D.connection (radialUnitField g) x w =
      (axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖) •
        (w - g.inner x (radialUnitField g x) w • radialUnitField g x) := by
  have hr := norm_pos_iff.mpr hx
  have ha := (amplitude_hasDerivAt g hr).comp_hasFDerivAt x (radius_hasFDerivAt hx)
  have hd := ha.smul (hasFDerivAt_id x)
  change HasFDerivAt (radialUnitField g) _ x at hd
  have hc := rotational_connection_const D hrotation hx w (radialUnitField g x)
  change D.euclideanConnection w (radialUnitField g x) x = _ at hc
  rw [D.connection_eq_fderiv_add
    ((radialUnitField_contDiffAt g hx).differentiableAt (by simp))]
  rw [hd.fderiv, hc, radialUnitField_projection g hrotation hx]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    radialUnitField, inner_smul_right, Function.comp_apply, id_eq,
    real_inner_self_eq_norm_sq, real_inner_comm w x]
  unfold axisWarpingSlope axisWarpingRadius
  change @Eq StandardCapSpace _ _
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hr.ne', (axisRadialSpeed_pos g ‖x‖).ne',
    (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g ‖x‖)).ne']
  ring

end PoincareConjecture.M35.Uniqueness
