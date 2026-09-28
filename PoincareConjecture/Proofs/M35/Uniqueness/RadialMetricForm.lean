import PoincareConjecture.Proofs.M35.Uniqueness.RadialAxisMetric
import PoincareConjecture.Proofs.M35.Uniqueness.AxisRotations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.M35.Uniqueness

private theorem euclidean_inner_coordinates (u v : StandardCapSpace) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring



theorem rotational_metric_form
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    g.inner x u v =
      axisAngularCoefficient g ‖x‖ * inner ℝ u v +
        (axisRadialCoefficient g ‖x‖ - axisAngularCoefficient g ‖x‖) *
          (inner ℝ x u * inner ℝ x v) / ‖x‖ ^ 2 := by
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let u' := standardRotation A⁻¹ u
  let v' := standardRotation A⁻¹ v
  let p : StandardCapSpace := ‖x‖ • EuclideanSpace.single 2 1
  have hu : standardRotation A u' = u := standardRotation_inv_apply A u
  have hv : standardRotation A v' = v := standardRotation_inv_apply A v
  have hg : g.inner x u v = g.inner p u' v' := by
    have h := hrotation A p u' v'
    rw [standardRotation_mfderiv] at h
    change g.inner (standardRotation A p) (standardRotation A u')
      (standardRotation A v') = g.inner p u' v' at h
    rw [hA, hu, hv] at h
    exact h
  have hrad (a a' : StandardCapSpace) (ha : standardRotation A a' = a) :
      inner ℝ x a = ‖x‖ * a' 2 := by
    calc
      _ = inner ℝ (standardRotation A p) (standardRotation A a') := by rw [hA, ha]
      _ = inner ℝ p a' := standardRotation_inner A p a'
      _ = _ := by simp [p, inner_smul_left, EuclideanSpace.inner_single_left]
  have huu := hrad u u' hu
  have hvv := hrad v v' hv
  have huv := standardRotation_inner A⁻¹ u v
  change inner ℝ u' v' = inner ℝ u v at huv
  rw [euclidean_inner_coordinates] at huv
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hprod : u' 2 * v' 2 = inner ℝ x u * inner ℝ x v / ‖x‖ ^ 2 := by
    rw [huu, hvv]
    field_simp [hnorm]
  rw [hg, rotational_axis_metric g hrotation]
  change axisAngularCoefficient g ‖x‖ * _ + axisRadialCoefficient g ‖x‖ * _ = _
  rw [← huv]
  rw [mul_div_assoc, ← hprod]
  ring



theorem rotational_metric_angular
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace)
    (hu : inner ℝ x u = 0) :
    g.inner x u v = axisAngularCoefficient g ‖x‖ * inner ℝ u v := by
  rw [rotational_metric_form g hrotation hx, hu, zero_mul, mul_zero, zero_div, add_zero]

end PoincareConjecture.M35.Uniqueness
