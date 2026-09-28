import PoincareConjecture.Proofs.M35.Uniqueness.CoordinateRotations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

theorem rotation_basis_zero (s : ℝ) :
    standardRotation (coordinateRotation s) (e 0) = Real.cos s • e 0 + Real.sin s • e 1 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, coordinateRotation, e, EuclideanSpace.single,
      dotProduct]

theorem rotation_basis_one (s : ℝ) :
    standardRotation (coordinateRotation s) (e 1) = -Real.sin s • e 0 + Real.cos s • e 1 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, coordinateRotation, e, EuclideanSpace.single,
      dotProduct]

theorem rotation_basis_two (s : ℝ) :
    standardRotation (coordinateRotation s) (e 2) = e 2 := by
  ext i
  fin_cases i <;>
    simp [standardRotation, coordinateRotation, e, EuclideanSpace.single,
      dotProduct]

theorem rotation_axis (s r : ℝ) :
    standardRotation (coordinateRotation s) (r • e 2) = r • e 2 := by
  change Matrix.toEuclideanLin (coordinateRotation s).1 (r • e 2) = _
  rw [map_smul]
  exact congrArg (r • ·) (rotation_basis_two s)



noncomputable def axisRadialCoefficient
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  g.inner (r • e 2) (e 2) (e 2)



noncomputable def axisAngularCoefficient
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  g.inner (r • e 2) (e 0) (e 0)



theorem rotational_axis_metric
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (r : ℝ) (u v : StandardCapSpace) :
    g.inner (r • e 2) u v =
      axisAngularCoefficient g r * (u 0 * v 0 + u 1 * v 1) +
        axisRadialCoefficient g r * (u 2 * v 2) := by
  let p := r • e 2
  have hrot (s : ℝ) (a b : StandardCapSpace) :
      g.inner p (standardRotation (coordinateRotation s) a)
        (standardRotation (coordinateRotation s) b) = g.inner p a b := by
    have h := hrotation (coordinateRotation s) p a b
    rw [standardRotation_mfderiv] at h
    change g.inner (standardRotation (coordinateRotation s) (r • e 2))
      (standardRotation (coordinateRotation s) a)
      (standardRotation (coordinateRotation s) b) = _ at h
    rw [rotation_axis] at h
    exact h
  have h20 : g.inner p (e 2) (e 0) = 0 := by
    have h := hrot Real.pi (e 2) (e 0)
    simp only [rotation_basis_two, rotation_basis_zero, Real.cos_pi, Real.sin_pi,
      neg_one_smul, zero_smul, add_zero, map_neg] at h
    linarith only [h]
  have h21 : g.inner p (e 2) (e 1) = 0 := by
    have h := hrot Real.pi (e 2) (e 1)
    simp only [rotation_basis_two, rotation_basis_one, Real.cos_pi, Real.sin_pi,
      neg_zero, zero_smul, neg_one_smul, zero_add, map_neg] at h
    linarith only [h]
  have h01 : g.inner p (e 0) (e 1) = 0 := by
    have h := hrot (Real.pi / 2) (e 0) (e 1)
    simp only [rotation_basis_zero, rotation_basis_one, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_smul, one_smul, zero_add, neg_one_smul, add_zero,
      map_neg, g.symm p (e 1) (e 0)] at h
    linarith only [h]
  have h11 : g.inner p (e 1) (e 1) = g.inner p (e 0) (e 0) := by
    have h := hrot (Real.pi / 2) (e 0) (e 0)
    simpa only [rotation_basis_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
      zero_smul, one_smul, zero_add] using h
  have h02 : g.inner p (e 0) (e 2) = 0 := (g.symm p _ _).trans h20
  have h12 : g.inner p (e 1) (e 2) = 0 := (g.symm p _ _).trans h21
  have h10 : g.inner p (e 1) (e 0) = 0 := (g.symm p _ _).trans h01
  have hexp (a : StandardCapSpace) : a = a 0 • e 0 + a 1 • e 1 + a 2 • e 2 := by
    ext i
    fin_cases i <;> simp [e, EuclideanSpace.single]
  calc
    _ = g.inner p (u 0 • e 0 + u 1 • e 1 + u 2 • e 2)
          (v 0 • e 0 + v 1 • e 1 + v 2 • e 2) := by
      rw [← hexp u, ← hexp v]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
        h20, h21, h01, h02, h12, h10, h11, mul_zero, zero_add, add_zero]
      change _ = g.inner p (e 0) (e 0) * _ + g.inner p (e 2) (e 2) * _
      ring


theorem axisRadialCoefficient_pos (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) :
    0 < axisRadialCoefficient g r := by
  apply g.pos
  intro h
  have hh := congrArg (fun v : StandardCapSpace => v 2) h
  simp [e, EuclideanSpace.single] at hh


theorem axisAngularCoefficient_pos (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) :
    0 < axisAngularCoefficient g r := by
  apply g.pos
  intro h
  have hh := congrArg (fun v : StandardCapSpace => v 0) h
  simp [e, EuclideanSpace.single] at hh

end PoincareConjecture.M35.Uniqueness
