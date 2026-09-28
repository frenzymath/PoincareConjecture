import PoincareConjecture.Proofs.M35.RawFlow.AxisAngularRicci
import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitRicci
import PoincareConjecture.Proofs.M13.ContractionTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation

theorem rotational_axis_ricci_form (r : ℝ) (u v : StandardCapSpace) :
    D.ricci (r • e 2) u v =
      D.ricci (r • e 2) (e 0) (e 0) * (u 0 * v 0 + u 1 * v 1) +
        D.ricci (r • e 2) (e 2) (e 2) * (u 2 * v 2) := by
  let p := r • e 2
  let B : StandardCapSpace →ₗ[ℝ] StandardCapSpace →ₗ[ℝ] ℝ := M13.ricciLinear D p
  have hsymm (a b : StandardCapSpace) : B a b = B b a := M04.ricci_symm D p a b
  have hrot (s : ℝ) (a b : StandardCapSpace) :
      B (standardRotation (coordinateRotation s) a)
        (standardRotation (coordinateRotation s) b) = B a b := by
    let f := standardRotationDiffeomorph (coordinateRotation s)
    have hf : MetricHomothety g g f 1 := by
      intro x u v
      change g.inner (standardRotation (coordinateRotation s) x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation (coordinateRotation s)) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation (coordinateRotation s)) x v) =
          1 * g.inner x u v
      simpa only [one_mul] using hrotation (coordinateRotation s) x u v
    have hh := M13.homothety_ricci_eq g g f 1 (by norm_num) hf D D p a b
    change D.ricci (standardRotation (coordinateRotation s) p)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation (coordinateRotation s)) p a)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation (coordinateRotation s)) p b) = _ at hh
    rw [standardRotation_mfderiv] at hh
    change D.ricci (standardRotation (coordinateRotation s) (r • e 2))
      (standardRotation (coordinateRotation s) a)
      (standardRotation (coordinateRotation s) b) = _ at hh
    rw [rotation_axis] at hh
    exact hh
  have h20 : B (e 2) (e 0) = 0 := by
    have h := hrot Real.pi (e 2) (e 0)
    simp only [rotation_basis_two, rotation_basis_zero, Real.cos_pi, Real.sin_pi,
      neg_one_smul, zero_smul, add_zero, map_neg] at h
    linarith only [h]
  have h21 : B (e 2) (e 1) = 0 := by
    have h := hrot Real.pi (e 2) (e 1)
    simp only [rotation_basis_two, rotation_basis_one, Real.cos_pi, Real.sin_pi,
      neg_zero, zero_smul, neg_one_smul, zero_add, map_neg] at h
    linarith only [h]
  have h01 : B (e 0) (e 1) = 0 := by
    have h := hrot (Real.pi / 2) (e 0) (e 1)
    simp only [rotation_basis_zero, rotation_basis_one, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_smul, one_smul, zero_add, neg_one_smul, add_zero,
      map_neg, hsymm (e 1) (e 0)] at h
    linarith only [h]
  have h11 : B (e 1) (e 1) = B (e 0) (e 0) := by
    have h := hrot (Real.pi / 2) (e 0) (e 0)
    simpa only [rotation_basis_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
      zero_smul, one_smul, zero_add] using h
  have h02 : B (e 0) (e 2) = 0 := (hsymm _ _).trans h20
  have h12 : B (e 1) (e 2) = 0 := (hsymm _ _).trans h21
  have h10 : B (e 1) (e 0) = 0 := (hsymm _ _).trans h01
  have hexp (a : StandardCapSpace) : a = a 0 • e 0 + a 1 • e 1 + a 2 • e 2 := by
    ext i
    fin_cases i <;> simp [e, EuclideanSpace.single]
  change B u v = B (e 0) (e 0) * _ + B (e 2) (e 2) * _
  calc
    _ = B (u 0 • e 0 + u 1 • e 1 + u 2 • e 2)
        (v 0 • e 0 + v 1 • e 1 + v 2 • e 2) := by rw [← hexp u, ← hexp v]
    _ = _ := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h20, h21, h01, h02, h12, h10, h11, mul_zero, zero_add, add_zero]
      ring

theorem radialMixedCurvatureFactor_eq_zero_of_ricci_null
    (hsec : D.NonnegativeSectionalCurvature) {r : ℝ} (hr : 0 < r)
    {v : StandardCapSpace} (hv : v ≠ 0) (hnull : D.ricci (r • e 2) v v = 0) :
    radialMixedCurvatureFactor g r = 0 := by
  have hk := radialMixedCurvatureFactor_nonneg D hrotation hsec hr
  apply le_antisymm _ hk
  by_contra hn
  have hK : 0 < radialMixedCurvatureFactor g r := lt_of_not_ge hn
  have ha : 0 ≤ radialTangentialCurvatureFactor g r := by
    have hh := hsec (r • e 2) (e 0) (e 1)
    rw [(rotational_sectional_numerators_axis D hrotation hr).1] at hh
    exact nonneg_of_mul_nonneg_right hh (axisAngularCoefficient_pos g r)
  have hangular : 0 < D.ricci (r • e 2) (e 0) (e 0) := by
    rw [rotational_axis_angular_ricci D hrotation hr]
    exact add_pos_of_nonneg_of_pos ha
      (div_pos (mul_pos (axisAngularCoefficient_pos g r) hK) (axisRadialCoefficient_pos g r))
  have hradial : 0 < D.ricci (r • e 2) (e 2) (e 2) := by
    rw [rotational_axis_radial_ricci D hrotation hr]
    positivity
  rw [rotational_axis_ricci_form D hrotation] at hnull
  have hn01 := mul_nonneg hangular.le (add_nonneg (sq_nonneg (v 0)) (sq_nonneg (v 1)))
  have hn2 := mul_nonneg hradial.le (sq_nonneg (v 2))
  have hz01 : v 0 ^ 2 + v 1 ^ 2 = 0 := by
    apply (mul_eq_zero.mp (show D.ricci (r • e 2) (e 0) (e 0) *
      (v 0 ^ 2 + v 1 ^ 2) = 0 by nlinarith only [hnull, hn01, hn2])).resolve_left hangular.ne'
  have hz2sq : v 2 ^ 2 = 0 := by
    apply (mul_eq_zero.mp (show D.ricci (r • e 2) (e 2) (e 2) * v 2 ^ 2 = 0 by
      nlinarith only [hnull, hn01, hn2])).resolve_left hradial.ne'
  have hz0 : v 0 = 0 := by nlinarith only [hz01, sq_nonneg (v 1)]
  have hz1 : v 1 = 0 := by nlinarith only [hz01, sq_nonneg (v 0)]
  have hz2 : v 2 = 0 := by nlinarith only [hz2sq]
  apply hv
  ext i
  fin_cases i <;> simp [hz0, hz1, hz2]

end PoincareConjecture.M35.Uniqueness
