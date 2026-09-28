import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicMetricCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

theorem intrinsicSpatialMetric_connection_beta {r : ℝ} (hr : 0 < r) :
    radialConnectionBeta (intrinsicSpatialMetric g hrotation hcomplete) r * r =
      (r - intrinsicWarpingRadius g hrotation hcomplete r *
        deriv (intrinsicWarpingRadius g hrotation hcomplete) r) / r ^ 2 := by
  let Q := intrinsicWarpingQuotient g hrotation hcomplete
  have hQ : ContDiff ℝ ∞ Q := intrinsicWarpingQuotient_contDiff g hrotation hcomplete
  have ha : axisAngularCoefficient (intrinsicSpatialMetric g hrotation hcomplete) =
      fun s => Q s ^ 2 :=
    funext (intrinsicSpatialMetric_axisAngularCoefficient g hrotation hcomplete)
  have had : deriv (axisAngularCoefficient
      (intrinsicSpatialMetric g hrotation hcomplete)) r = 2 * Q r * deriv Q r := by
    rw [ha]
    have h := (hQ.differentiable (by simp) r).hasDerivAt.pow 2
    change HasDerivAt (fun s => Q s ^ 2) (2 * Q r ^ (2 - 1) * deriv Q r) r at h
    simpa only [Nat.reduceSub, pow_one] using h.deriv
  have hf : (fun s => s * Q s) = intrinsicWarpingRadius g hrotation hcomplete :=
    funext (mul_intrinsicWarpingQuotient g hrotation hcomplete)
  have hfd : deriv (intrinsicWarpingRadius g hrotation hcomplete) r =
      Q r + r * deriv Q r := by
    have h := (hasDerivAt_id r).mul (hQ.differentiable (by simp) r).hasDerivAt
    change HasDerivAt (fun s => s * Q s) (1 * Q r + r * deriv Q r) r at h
    rw [hf] at h
    simpa only [one_mul] using h.deriv
  rw [radialConnectionBeta, axisCorrectionCoefficient,
    intrinsicSpatialMetric_axisRadialCoefficient, had,
    intrinsicSpatialMetric_axisAngularCoefficient, div_one, hfd, ← congrFun hf r]
  change ((1 - Q r ^ 2) / r ^ 2 - 2 * Q r * deriv Q r / (2 * r)) * r = _
  field_simp [hr.ne']
  ring

theorem intrinsicSpatialMetric_connection_radial {r : ℝ} (hr : 0 < r) :
    2 * radialConnectionAlpha (intrinsicSpatialMetric g hrotation hcomplete) r +
      radialConnectionBeta (intrinsicSpatialMetric g hrotation hcomplete) r +
      radialConnectionGamma (intrinsicSpatialMetric g hrotation hcomplete) r * r ^ 2 = 0 := by
  have h := axisRadialCoefficient_deriv_eq_connection
    (intrinsicSpatialMetric g hrotation hcomplete) hr
  rw [intrinsicSpatialMetric_radial_deriv, intrinsicSpatialMetric_axisRadialCoefficient,
    mul_one] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by norm_num) hr.ne')

variable (D : LeviCivitaData (intrinsicSpatialMetric g hrotation hcomplete))

theorem intrinsicSpatialMetric_connection_angular {r : ℝ} (hr : 0 < r)
    (i : Fin 3) (hi : i ≠ 2) :
    D.euclideanConnection (e i) (e i) (r • e 2) =
      ((r - intrinsicWarpingRadius g hrotation hcomplete r *
        deriv (intrinsicWarpingRadius g hrotation hcomplete) r) / r ^ 2) • e 2 := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have h := rotational_connection_const D
    (intrinsicSpatialMetric_rotation g hrotation hcomplete) hx (e i) (e i)
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e i) = 0 := by
    fin_cases i <;> simp_all [e, EuclideanSpace.inner_single_left, inner_smul_left]
  have hei : inner ℝ (e i) (e i) = 1 := by simp [e]
  change D.connection (fun _ : StandardCapSpace => e i) (r • e 2) (e i) = _
  rw [h, hn, hxe, hei]
  simp only [zero_smul, add_zero, smul_zero, mul_one, mul_zero, smul_smul, zero_add]
  rw [intrinsicSpatialMetric_connection_beta g hrotation hcomplete hr]

theorem intrinsicSpatialMetric_connection_axis {r : ℝ} (hr : 0 < r) :
    D.euclideanConnection (e 2) (e 2) (r • e 2) = 0 := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have h := rotational_connection_const D
    (intrinsicSpatialMetric_rotation g hrotation hcomplete) hx (e 2) (e 2)
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e 2) = r := by simp [e, inner_smul_left]
  have hei : inner ℝ (e 2) (e 2) = 1 := by simp [e]
  change D.connection (fun _ : StandardCapSpace => e 2) (r • e 2) (e 2) = 0
  rw [h, hn, hxe, hei]
  have hc := intrinsicSpatialMetric_connection_radial g hrotation hcomplete hr
  calc
    _ = (r * (2 * radialConnectionAlpha (intrinsicSpatialMetric g hrotation hcomplete) r +
        radialConnectionBeta (intrinsicSpatialMetric g hrotation hcomplete) r +
        radialConnectionGamma (intrinsicSpatialMetric g hrotation hcomplete) r * r ^ 2)) •
          e 2 := by module
    _ = 0 := by rw [hc, mul_zero, zero_smul]

end PoincareConjecture.M35.Uniqueness
