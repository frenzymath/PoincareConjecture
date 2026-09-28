import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialDifferential
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicTip
import PoincareConjecture.Proofs.M35.Uniqueness.RadialMetricForm
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.GaugePullbackMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation in
theorem rotational_rescale_form {x : StandardCapSpace} (hx : x ≠ 0)
    {k : ℝ} (hk : 0 < k) (l : ℝ) (u v : StandardCapSpace) :
    g.inner (k • x) (k • u + (l * inner ℝ x u) • x)
      (k • v + (l * inner ℝ x v) • x) =
    axisAngularCoefficient g (k * ‖x‖) * k ^ 2 * inner ℝ u v +
      (axisRadialCoefficient g (k * ‖x‖) * (k + l * ‖x‖ ^ 2) ^ 2 -
        axisAngularCoefficient g (k * ‖x‖) * k ^ 2) *
          (inner ℝ x u * inner ℝ x v) / ‖x‖ ^ 2 := by
  rw [rotational_metric_form g hrotation (smul_ne_zero hk.ne' hx),
    _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u x]
  field_simp [hk.ne', norm_ne_zero_iff.mpr hx]
  ring

variable (hcomplete : MetricComplete g)


noncomputable def intrinsicSpatialMetric : RiemannianMetric 3 StandardCapSpace :=
  gaugePullbackMetric g (intrinsicSpatialDiffeomorph g hrotation hcomplete).symm

theorem intrinsicSpatialMetric_pullback (x u v : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).inner x u v =
      g.inner (intrinsicSpatialInverse g hrotation hcomplete x)
        (fderiv ℝ (intrinsicSpatialInverse g hrotation hcomplete) x u)
        (fderiv ℝ (intrinsicSpatialInverse g hrotation hcomplete) x v) := by
  rw [intrinsicSpatialMetric, gaugePullbackMetric_inner]
  rfl


theorem intrinsicSpatialMetric_inner {x : StandardCapSpace} (hx : x ≠ 0)
    (u v : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).inner x u v =
      intrinsicWarpingQuotient g hrotation hcomplete ‖x‖ ^ 2 * inner ℝ u v +
        (1 - intrinsicWarpingQuotient g hrotation hcomplete ‖x‖ ^ 2) *
          (inner ℝ x u * inner ℝ x v) / ‖x‖ ^ 2 := by
  let r := ‖x‖
  let q := (radialArclengthOrderIso g hrotation hcomplete).symm r
  let k := intrinsicInverseScale g hrotation hcomplete r
  let l := axisDivision (deriv (intrinsicInverseScale g hrotation hcomplete)) r
  let Q := intrinsicWarpingQuotient g hrotation hcomplete r
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hk : 0 < k := intrinsicInverseScale_pos g hrotation hcomplete hr
  have hkq : k * r = q := by
    simpa only [mul_comm] using mul_intrinsicInverseScale g hrotation hcomplete r
  have hspeed : k + l * r ^ 2 = (Real.sqrt (axisRadialCoefficient g q))⁻¹ := by
    simpa only [mul_comm] using
      intrinsicInverseScale_radial_derivative g hrotation hcomplete r
  have hrad : axisRadialCoefficient g q * (k + l * r ^ 2) ^ 2 = 1 := by
    rw [hspeed, inv_pow, Real.sq_sqrt (axisRadialCoefficient_pos g q).le]
    exact mul_inv_cancel₀ (axisRadialCoefficient_pos g q).ne'
  have hQ : Q = k * Real.sqrt (axisAngularCoefficient g q) := by
    apply mul_left_cancel₀ hr.ne'
    calc
      r * Q = intrinsicWarpingRadius g hrotation hcomplete r :=
        mul_intrinsicWarpingQuotient g hrotation hcomplete r
      _ = q * Real.sqrt (axisAngularCoefficient g q) := rfl
      _ = r * (k * Real.sqrt (axisAngularCoefficient g q)) := by rw [← hkq]; ring
  have hang : axisAngularCoefficient g q * k ^ 2 = Q ^ 2 := by
    rw [hQ, mul_pow, Real.sq_sqrt (axisAngularCoefficient_pos g q).le]
    ring
  rw [intrinsicSpatialMetric_pullback, intrinsicSpatialInverse_fderiv,
    intrinsicSpatialInverse_fderiv]
  change g.inner (k • x) (k • u + (l * inner ℝ x u) • x)
    (k • v + (l * inner ℝ x v) • x) = _
  rw [rotational_rescale_form g hrotation hx hk]
  change axisAngularCoefficient g (k * r) * k ^ 2 * inner ℝ u v +
    (axisRadialCoefficient g (k * r) * (k + l * r ^ 2) ^ 2 -
      axisAngularCoefficient g (k * r) * k ^ 2) *
        (inner ℝ x u * inner ℝ x v) / r ^ 2 = _
  rw [hkq, hrad, hang]

include hrotation in
private theorem rotational_metric_origin (u v : StandardCapSpace) :
    g.inner 0 u v = axisRadialCoefficient g 0 * inner ℝ u v := by
  have h := rotational_axis_metric g hrotation 0 u v
  rw [zero_smul, axisAngularCoefficient_zero_eq_radial g hrotation] at h
  rw [h]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring


theorem intrinsicSpatialMetric_inner_zero (u v : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).inner 0 u v = inner ℝ u v := by
  rw [intrinsicSpatialMetric_pullback, intrinsicSpatialInverse_zero,
    intrinsicSpatialInverse_fderiv_zero, intrinsicSpatialInverse_fderiv_zero,
    rotational_metric_origin g hrotation]
  rw [real_inner_smul_left, real_inner_smul_right]
  have hs := Real.sq_sqrt (axisRadialCoefficient_pos g 0).le
  have hc : axisRadialCoefficient g 0 *
      (Real.sqrt (axisRadialCoefficient g 0))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, hs]
    exact mul_inv_cancel₀ (axisRadialCoefficient_pos g 0).ne'
  calc
    _ = (axisRadialCoefficient g 0 *
        (Real.sqrt (axisRadialCoefficient g 0))⁻¹ ^ 2) * inner ℝ u v := by ring
    _ = _ := by rw [hc, one_mul]

end PoincareConjecture.M35.Uniqueness
