import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1



theorem exists_axis_radial_sectional_plane
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {r : ℝ} (hr : 0 < r) :
    ∃ u v : StandardCapSpace,
      g.inner (r • e 2) u u = 1 ∧ g.inner (r • e 2) v v = 1 ∧
      g.inner (r • e 2) u v = 0 ∧
      D.curvatureTensor (r • e 2) u v u v =
        radialMixedCurvatureFactor g r / axisRadialCoefficient g r := by
  let a := axisAngularCoefficient g r
  let b := axisRadialCoefficient g r
  have ha : 0 < a := axisAngularCoefficient_pos g r
  have hb : 0 < b := axisRadialCoefficient_pos g r
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have h00 : g.inner (r • e 2) (e 0) (e 0) = a := rfl
  have h22 : g.inner (r • e 2) (e 2) (e 2) = b := rfl
  have h02 : g.inner (r • e 2) (e 0) (e 2) = 0 := by
    rw [rotational_axis_metric g hrotation]
    simp [e]
  let u := (Real.sqrt a)⁻¹ • e 0
  let v := (Real.sqrt b)⁻¹ • e 2
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · simp only [u, map_smul, smul_apply, smul_eq_mul, h00]
    field_simp [hsa]
    exact (Real.sq_sqrt ha.le).symm
  · simp only [v, map_smul, smul_apply, smul_eq_mul, h22]
    field_simp [hsb]
    exact (Real.sq_sqrt hb.le).symm
  · simp only [u, v, map_smul, smul_apply, smul_eq_mul, h02, mul_zero]
  · simp only [u, v, D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
      D.curvatureTensor_smul_third, D.curvatureTensor_smul_last]
    rw [(rotational_sectional_numerators_axis D hrotation hr).2.1]
    change (Real.sqrt a)⁻¹ * ((Real.sqrt b)⁻¹ *
      ((Real.sqrt a)⁻¹ * ((Real.sqrt b)⁻¹ * (a * radialMixedCurvatureFactor g r)))) =
        radialMixedCurvatureFactor g r / b
    field_simp [hsa, hsb, hb.ne']
    rw [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    ring



theorem exists_radial_sectional_plane
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ∃ u v : StandardCapSpace,
      g.inner x u u = 1 ∧ g.inner x v v = 1 ∧ g.inner x u v = 0 ∧
      D.curvatureTensor x u v u v =
        radialMixedCurvatureFactor g ‖x‖ / axisRadialCoefficient g ‖x‖ := by
  obtain ⟨u, v, hu, hv, huv, hcurv⟩ :=
    exists_axis_radial_sectional_plane D hrotation (norm_pos_iff.mpr hx)
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let f := standardRotationDiffeomorph A
  let p := ‖x‖ • e 2
  have hfx : f p = x := hA
  have hf : MetricHomothety g g f 1 := by
    intro y u v
    change g.inner (standardRotation A y)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y v) = _
    simpa only [one_mul] using hrotation A y u v
  refine ⟨mfderiv (𝓡 3) (𝓡 3) f p u, mfderiv (𝓡 3) (𝓡 3) f p v, ?_, ?_, ?_, ?_⟩
  · rw [← hfx, hf, one_mul]
    exact hu
  · rw [← hfx, hf, one_mul]
    exact hv
  · rw [← hfx, hf, one_mul]
    exact huv
  · rw [← hfx, M13.homothety_curvatureTensor_eq g g f 1 hf D D, one_mul]
    rw [hfx]
    exact hcurv

end PoincareConjecture.M35.Uniqueness
