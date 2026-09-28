import PoincareConjecture.Proofs.M36.CylinderPlaneBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem cylinderHeightCovector_abs_le_norm (v : E₃) :
    |cylinderHeightCovector v| ≤ ‖v‖ := by
  have h := cylinderHeightCovector_sq_le_norm_sq v
  nlinarith only [h, sq_abs (cylinderHeightCovector v),
    abs_nonneg (cylinderHeightCovector v), norm_nonneg v]

theorem cylinderHeightCovector_norm_le_one : ‖cylinderHeightCovector‖ ≤ 1 := by
  apply cylinderHeightCovector.opNorm_le_bound zero_le_one
  intro v
  simpa only [Real.norm_eq_abs, one_mul] using cylinderHeightCovector_abs_le_norm v

theorem cylinderModelField_vertical (u : E₃) :
    cylinderModelField 0 u (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      cylinderHeightCovector u := by
  have hP : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ 2) = 0 := by
    change (cylinderEuclideanEquiv (EuclideanSpace.basisFun (Fin 3) ℝ 2)).1 = 0
    rw [cylinderEuclideanEquiv_basis]
    rfl
  have hd : cylinderHeightCovector (EuclideanSpace.basisFun (Fin 3) ℝ 2) = 1 := by
    rw [cylinderHeightCovector_basis]
    rfl
  rw [cylinderModelField_zero]
  change 2 * inner ℝ (cylinderHorizontalProjection u)
      (cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ 2)) +
    cylinderHeightCovector u * cylinderHeightCovector (EuclideanSpace.basisFun (Fin 3) ℝ 2) = _
  rw [hP, hd, inner_zero_right, mul_zero, zero_add, mul_one]

theorem cylinder_close_bilinear_lower
    (A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) {rho : ℝ} (hsmall : rho ≤ 1 / 2)
    (hA : ‖A - cylinderModelField 0‖ ≤ rho) (v : E₃) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ A v v := by
  have he : |A v v - cylinderModelField 0 v v| ≤ rho * ‖v‖ * ‖v‖ := by
    exact ((A - cylinderModelField 0).le_opNorm₂ v v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
        (norm_nonneg v))
  have h := (abs_le.mp he).1
  have hmodel := cylinderModelField_zero_lower v
  have hr := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)
  nlinarith only [h, hmodel, hr]

theorem cylinder_close_dual_height
    (A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) {rho : ℝ} (hrho : 0 ≤ rho)
    (hsmall : rho ≤ 1 / 2) (hA : ‖A - cylinderModelField 0‖ ≤ rho)
    (U : E₃) (hU : ∀ v : E₃, A U v = cylinderHeightCovector v) :
    ‖U‖ ≤ 2 ∧ |A U U - 1| ≤ 2 * rho := by
  have hlo := cylinder_close_bilinear_lower A hsmall hA U
  rw [hU U] at hlo
  have hu := (abs_le.mp (cylinderHeightCovector_abs_le_norm U)).2
  have hn : ‖U‖ ≤ 2 := by nlinarith only [hlo, hu, norm_nonneg U]
  refine ⟨hn, ?_⟩
  let e := EuclideanSpace.basisFun (Fin 3) ℝ 2
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 2
  have hd : cylinderHeightCovector e = 1 := by
    rw [cylinderHeightCovector_basis]
    rfl
  have hbound : |A U e - cylinderModelField 0 U e| ≤ rho * ‖U‖ := by
    have h := ((A - cylinderModelField 0).le_opNorm₂ U e).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg U))
        (norm_nonneg e))
    simpa only [sub_apply, Real.norm_eq_abs, he, mul_one] using h
  rw [hU e, hd, cylinderModelField_vertical] at hbound
  rw [hU U, abs_sub_comm]
  exact hbound.trans (by nlinarith only [mul_le_mul_of_nonneg_left hn hrho])

end PoincareConjecture.M36
