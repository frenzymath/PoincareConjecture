import PoincareConjecture.Proofs.M35.CapGeometry.RadialShapeDerivative
import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1



theorem rotational_axis_radial_ricci
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    D.ricci (r • e 2) (e 2) (e 2) = 2 * radialMixedCurvatureFactor g r := by
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
  have hricci : D.ricci p (e 2) (e 2) =
      ∑ j : Fin 3, (w j)⁻¹ * D.curvatureTensor p (e 2) (b j) (e 2) (b j) := by
    rw [D.ricci_eq_inverse_gram p b A hA (e 2) (e 2), hgram, Matrix.inv_diagonal]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hinv]
  obtain ⟨_h01, h02, h12⟩ := rotational_sectional_numerators_axis D hrotation hr
  have h20 := (D.curvatureTensor_diagonal_pair_swap p (e 2) (e 0)).trans h02
  have h21 := (D.curvatureTensor_diagonal_pair_swap p (e 2) (e 1)).trans h12
  rw [hricci]
  simp only [hb, Fin.sum_univ_three]
  erw [h20, h21]
  simp only [D.curvatureTensor_zero_first, mul_zero, add_zero,
    w, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [(axisAngularCoefficient_pos g r).ne']
  ring



theorem radialUnitField_axis
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    radialUnitField g (r • e 2) = (axisRadialSpeed g r)⁻¹ • e 2 := by
  have hn : ‖r • e 2‖ = r := by
    simp [norm_smul, e, abs_of_pos hr]
  simp only [radialUnitField, hn, smul_smul]
  congr 1
  field_simp [hr.ne']



theorem radialUnitField_ricci
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    D.ricci x (radialUnitField g x) (radialUnitField g x) =
      2 * radialMixedCurvatureFactor g ‖x‖ / axisRadialCoefficient g ‖x‖ := by
  have hr := norm_pos_iff.mpr hx
  let p := ‖x‖ • e 2
  have hn : ‖p‖ = ‖x‖ := by
    simp [p, norm_smul, e]
  have haxis : D.ricci p (radialUnitField g p) (radialUnitField g p) =
      2 * radialMixedCurvatureFactor g ‖x‖ / axisRadialCoefficient g ‖x‖ := by
    rw [radialUnitField_axis g hr]
    change M13.ricciLinear D p ((axisRadialSpeed g ‖x‖)⁻¹ • e 2)
      ((axisRadialSpeed g ‖x‖)⁻¹ • e 2) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
    rw [rotational_axis_radial_ricci D hrotation hr]
    unfold axisRadialSpeed
    field_simp [(Real.sqrt_pos.mpr (axisRadialCoefficient_pos g ‖x‖)).ne',
      (axisRadialCoefficient_pos g ‖x‖).ne']
    rw [Real.sq_sqrt (axisRadialCoefficient_pos g ‖x‖).le]
    ring
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let f := standardRotationDiffeomorph A
  have hfx : f p = x := hA
  have hf : MetricHomothety g g f 1 := by
    intro y u v
    change g.inner (standardRotation A y)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y v) = _
    simpa only [one_mul] using hrotation A y u v
  have hvector : mfderiv (𝓡 3) (𝓡 3) f p (radialUnitField g p) = radialUnitField g x := by
    change mfderiv (𝓡 3) (𝓡 3) (standardRotation A) p (radialUnitField g p) = _
    rw [standardRotation_mfderiv]
    simp only [radialUnitField, hn]
    change Matrix.toEuclideanLin A.1 ((‖x‖ * axisRadialSpeed g ‖x‖)⁻¹ • p) = _
    rw [map_smul]
    exact congrArg ((‖x‖ * axisRadialSpeed g ‖x‖)⁻¹ • ·) hfx
  have h := M13.homothety_ricci_eq g g f 1 zero_lt_one hf D D p
    (radialUnitField g p) (radialUnitField g p)
  have hv : mfderiv (𝓡 3) (𝓡 3) f p (radialUnitField g p) =
      radialUnitField g (f p) := hvector.trans (congrArg (radialUnitField g) hfx).symm
  rw [hv] at h
  have he := h.trans haxis
  change (fun y => D.ricci y (radialUnitField g y) (radialUnitField g y)) (f p) = _ at he
  rw [hfx] at he
  exact he

end PoincareConjecture.M35.Uniqueness
