import PoincareConjecture.Proofs.M35.Uniqueness.RadialMetricForm
import PoincareConjecture.Proofs.M35.Uniqueness.RadialArclength

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

noncomputable def axisCorrectionCoefficient
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  (axisRadialCoefficient g r - axisAngularCoefficient g r) / r ^ 2

theorem rotational_metric_form_correction
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    g.inner x u v = axisAngularCoefficient g ‖x‖ * inner ℝ u v +
      axisCorrectionCoefficient g ‖x‖ * inner ℝ x u * inner ℝ x v := by
  rw [rotational_metric_form g hrotation hx]
  unfold axisCorrectionCoefficient
  ring

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

theorem rotational_metric_first_derivative
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    fderiv ℝ (fun y => g.inner y v w) x u =
      deriv (axisAngularCoefficient g) ‖x‖ / ‖x‖ * inner ℝ x u * inner ℝ v w +
        deriv (axisCorrectionCoefficient g) ‖x‖ / ‖x‖ *
          inner ℝ x u * inner ℝ x v * inner ℝ x w +
        axisCorrectionCoefficient g ‖x‖ *
          (inner ℝ u v * inner ℝ x w + inner ℝ x v * inner ℝ u w) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) ‖x‖).hasDerivAt
  have hc : DifferentiableAt ℝ (axisCorrectionCoefficient g) ‖x‖ := by
    exact (((axisRadialCoefficient_contDiff g).differentiable (by simp) ‖x‖).sub
      ((axisAngularCoefficient_contDiff g).differentiable (by simp) ‖x‖)).div
        (differentiableAt_id.pow 2) (pow_ne_zero 2 hn)
  have hA := ha.comp_hasFDerivAt x (radius_hasFDerivAt hx)
  have hC := hc.hasDerivAt.comp_hasFDerivAt x (radius_hasFDerivAt hx)
  have hV := (innerSL ℝ v).hasFDerivAt (x := x)
  have hW := (innerSL ℝ w).hasFDerivAt (x := x)
  have hd := (hA.mul_const (inner ℝ v w)).add ((hC.mul hV).mul hW)
  change HasFDerivAt (fun y : StandardCapSpace =>
    axisAngularCoefficient g ‖y‖ * inner ℝ v w +
      axisCorrectionCoefficient g ‖y‖ * inner ℝ v y * inner ℝ w y) _ x at hd
  have heq : (fun y : StandardCapSpace => g.inner y v w) =ᶠ[𝓝 x]
      (fun y => axisAngularCoefficient g ‖y‖ * inner ℝ v w +
        axisCorrectionCoefficient g ‖y‖ * inner ℝ v y * inner ℝ w y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [rotational_metric_form g hrotation hy]
    simp only [axisCorrectionCoefficient, real_inner_comm v y, real_inner_comm w y]
    ring
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [add_apply, smul_apply, Pi.mul_apply, Function.comp_apply,
    smul_eq_mul, innerSL_apply_apply,
    real_inner_comm v x, real_inner_comm w x, real_inner_comm v u, real_inner_comm w u]
  ring

theorem rotational_inner_connection_const
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    2 * g.inner x (D.connection (fun _ : StandardCapSpace => v) x u) w =
      deriv (axisAngularCoefficient g) ‖x‖ / ‖x‖ *
        (inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w -
          inner ℝ x w * inner ℝ u v) +
        deriv (axisCorrectionCoefficient g) ‖x‖ / ‖x‖ *
          inner ℝ x u * inner ℝ x v * inner ℝ x w +
        2 * axisCorrectionCoefficient g ‖x‖ * inner ℝ u v * inner ℝ x w := by
  rw [D.inner_connection_const,
    rotational_metric_first_derivative g hrotation hx,
    rotational_metric_first_derivative g hrotation hx,
    rotational_metric_first_derivative g hrotation hx]
  rw [real_inner_comm w u, real_inner_comm v u, real_inner_comm w v]
  ring

end PoincareConjecture.M35.Uniqueness
