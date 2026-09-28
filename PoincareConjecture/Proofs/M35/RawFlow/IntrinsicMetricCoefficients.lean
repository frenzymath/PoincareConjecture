import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialMetric

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

theorem intrinsicSpatialMetric_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x u v : StandardCapSpace) :
    (intrinsicSpatialMetric g hrotation hcomplete).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
        (intrinsicSpatialMetric g hrotation hcomplete).inner x u v := by
  rw [standardRotation_mfderiv]
  change (intrinsicSpatialMetric g hrotation hcomplete).inner (standardRotation A x)
    (standardRotation A u) (standardRotation A v) = _
  have hn : ‖standardRotation A x‖ = ‖x‖ := by
    have h := standardRotation_inner A x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (standardRotation A x), norm_nonneg x]
  by_cases hx : x = 0
  · subst x
    have hz : standardRotation A 0 = 0 := map_zero (Matrix.toEuclideanLin A.1)
    rw [hz, intrinsicSpatialMetric_inner_zero, intrinsicSpatialMetric_inner_zero]
    exact standardRotation_inner A u v
  have hAx : standardRotation A x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    exact hx (norm_eq_zero.mp hn.symm)
  rw [intrinsicSpatialMetric_inner g hrotation hcomplete hAx,
    intrinsicSpatialMetric_inner g hrotation hcomplete hx, hn,
    standardRotation_inner, standardRotation_inner, standardRotation_inner]

private theorem quotient_abs (r : ℝ) :
    intrinsicWarpingQuotient g hrotation hcomplete |r| =
      intrinsicWarpingQuotient g hrotation hcomplete r := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
  · rw [abs_of_nonpos hr, intrinsicWarpingQuotient_even]

theorem intrinsicSpatialMetric_axisAngularCoefficient (r : ℝ) :
    axisAngularCoefficient (intrinsicSpatialMetric g hrotation hcomplete) r =
      intrinsicWarpingQuotient g hrotation hcomplete r ^ 2 := by
  change (intrinsicSpatialMetric g hrotation hcomplete).inner (r • e 2) (e 0) (e 0) = _
  by_cases hr : r = 0
  · subst r
    rw [zero_smul, intrinsicSpatialMetric_inner_zero, intrinsicWarpingQuotient_zero]
    simp [e]
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr (by simp [e])
  rw [intrinsicSpatialMetric_inner g hrotation hcomplete hx]
  simp [e, _root_.norm_smul, Real.norm_eq_abs, inner_smul_left,
    EuclideanSpace.inner_single_left, quotient_abs]

theorem intrinsicSpatialMetric_axisRadialCoefficient (r : ℝ) :
    axisRadialCoefficient (intrinsicSpatialMetric g hrotation hcomplete) r = 1 := by
  change (intrinsicSpatialMetric g hrotation hcomplete).inner (r • e 2) (e 2) (e 2) = _
  by_cases hr : r = 0
  · subst r
    rw [zero_smul, intrinsicSpatialMetric_inner_zero]
    simp [e]
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr (by simp [e])
  rw [intrinsicSpatialMetric_inner g hrotation hcomplete hx]
  simp only [_root_.norm_smul, Real.norm_eq_abs]
  have he : inner ℝ (e 2) (e 2) = 1 := by simp [e]
  have hen : ‖e 2‖ = 1 := by simp [e]
  rw [hen, mul_one, quotient_abs, he]
  simp only [real_inner_smul_left, he, mul_one, sq_abs]
  field_simp [hr]
  ring

theorem intrinsicSpatialMetric_radial_deriv (r : ℝ) :
    deriv (axisRadialCoefficient (intrinsicSpatialMetric g hrotation hcomplete)) r = 0 := by
  have heq : axisRadialCoefficient (intrinsicSpatialMetric g hrotation hcomplete) =
      fun _ : ℝ => 1 := funext (intrinsicSpatialMetric_axisRadialCoefficient g hrotation hcomplete)
  rw [heq, deriv_const]

end PoincareConjecture.M35.Uniqueness
