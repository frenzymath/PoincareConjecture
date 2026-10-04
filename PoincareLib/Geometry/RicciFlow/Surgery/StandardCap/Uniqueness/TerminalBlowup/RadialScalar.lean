import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.TerminalBlowup.RadialCurvature

/-!
# The actual scalar trace in radial form

Morgan-Tian Section 12.6, pp. 307-309. The actual axis coordinate frame
is orthogonal, with two angular weights a and radial weight b. Tracing
the retained curvature twice with the inverse Gram matrix gives
2 K_tan + 4 K_rad, before expressing those factors in arclength.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

/-- Section 12.6: the actual retained scalar is the sum of two angular
and four radial sectional curvatures in the genuine rotational metric. -/
theorem rotational_scalar_axis
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    D.scalarCurvature (r • e 2) =
      2 * radialTangentialCurvatureFactor g r / axisAngularCoefficient g r +
        4 * radialMixedCurvatureFactor g r / axisRadialCoefficient g r := by
  let p := r • e 2
  let w : Fin 3 → ℝ :=
    ![axisAngularCoefficient g r, axisAngularCoefficient g r, axisRadialCoefficient g r]
  let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) p) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hb (i : Fin 3) : b i = e i := EuclideanSpace.basisFun_apply (Fin 3) ℝ i
  have hgram : Matrix.of (fun i j : Fin 3 => g.inner p (b i) (b j)) =
      Matrix.diagonal w := by
    ext i j
    simp only [Matrix.of_apply, p, hb, rotational_axis_metric g hrotation]
    fin_cases i <;> fin_cases j <;> simp [e, w, Matrix.diagonal]
  have hw (i : Fin 3) : w i ≠ 0 := by
    fin_cases i
    · exact (axisAngularCoefficient_pos g r).ne'
    · exact (axisAngularCoefficient_pos g r).ne'
    · exact (axisRadialCoefficient_pos g r).ne'
  have hunit : IsUnit w := Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hw i))
  have hinv (i : Fin 3) : Ring.inverse w i = (w i)⁻¹ := by
    have h := congrFun (Ring.inverse_mul_cancel w hunit) i
    rw [← one_div]
    exact (eq_div_iff (hw i)).mpr h
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor p
  have hricci (i : Fin 3) : D.ricci p (b i) (b i) =
      ∑ j : Fin 3, (w j)⁻¹ * D.curvatureTensor p (b i) (b j) (b i) (b j) := by
    rw [D.ricci_eq_inverse_gram p b A hA (b i) (b i), hgram, Matrix.inv_diagonal]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hinv]
  have hscalar := scalarCurvature_eq_inverse_gram D p b
  rw [hgram, Matrix.inv_diagonal] at hscalar
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, hinv] at hscalar
  simp_rw [hricci] at hscalar
  obtain ⟨h01, h02, h12⟩ := rotational_sectional_numerators_axis D hrotation hr
  have h10 := (D.curvatureTensor_diagonal_pair_swap p (e 1) (e 0)).trans h01
  have h20 := (D.curvatureTensor_diagonal_pair_swap p (e 2) (e 0)).trans h02
  have h21 := (D.curvatureTensor_diagonal_pair_swap p (e 2) (e 1)).trans h12
  simp only [hb, Fin.sum_univ_succ, Fin.sum_univ_zero] at hscalar
  erw [h01, h02, h12, h10, h20, h21] at hscalar
  simp only [D.curvatureTensor_zero_first, mul_zero, add_zero, zero_add] at hscalar
  rw [hscalar]
  simp only [w, Matrix.cons_val_zero, Matrix.cons_val_succ]
  field_simp [(axisAngularCoefficient_pos g r).ne', (axisRadialCoefficient_pos g r).ne']
  ring

/-- Section 12.6: nonnegative sectional curvature makes the actual
radial curvature factor nonnegative, without any scalar assumption. -/
theorem radialMixedCurvatureFactor_nonneg
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hsec : D.NonnegativeSectionalCurvature) {r : ℝ} (hr : 0 < r) :
    0 ≤ radialMixedCurvatureFactor g r := by
  have h := hsec (r • e 2) (e 0) (e 2)
  rw [(rotational_sectional_numerators_axis D hrotation hr).2.1] at h
  exact nonneg_of_mul_nonneg_right h (axisAngularCoefficient_pos g r)

end PoincareMT.M35.Uniqueness
