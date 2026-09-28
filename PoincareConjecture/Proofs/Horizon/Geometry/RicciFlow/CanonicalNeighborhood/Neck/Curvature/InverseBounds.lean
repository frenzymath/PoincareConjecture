import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.InverseEstimate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace

namespace PoincareConjecture

private theorem cylinder_tail_norm_le (v : EuclideanSpace ℝ (Fin 3)) :
    ‖Poincare.EuclideanSpace.euclideanTail v‖ ≤ ‖v‖ := by
  have h : ‖Poincare.EuclideanSpace.euclideanTail v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, Poincare.EuclideanSpace.euclideanTail_apply]
    nlinarith [sq_nonneg (v 0)]
  nlinarith [norm_nonneg v, norm_nonneg (Poincare.EuclideanSpace.euclideanTail v)]

theorem roundCylinderEuclideanCoefficients_norm_zero_le :
    ‖roundCylinderEuclideanCoefficients 0‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num)
  intro v w
  have heq : roundCylinderEuclideanCoefficients 0 v w =
      ⟪v, w⟫_ℝ + ⟪Poincare.EuclideanSpace.euclideanTail v,
        Poincare.EuclideanSpace.euclideanTail w⟫_ℝ := by
    change roundCylinderModelCoefficients
      ((RiemannianMetric.lineModelEquiv 2).symm 0)
      ((RiemannianMetric.lineModelEquiv 2).symm v)
      ((RiemannianMetric.lineModelEquiv 2).symm w) = _
    simp only [map_zero, roundCylinderModelCoefficients_apply, Prod.fst_zero,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    change 2 * (16 / (4 : ℝ) ^ 2) *
      ⟪Poincare.EuclideanSpace.euclideanTail v,
        Poincare.EuclideanSpace.euclideanTail w⟫_ℝ + v 0 * w 0 = _
    norm_num
    simp only [PiLp.inner_apply, Fin.sum_univ_succ,
      Poincare.EuclideanSpace.euclideanTail_apply, RCLike.inner_apply, conj_trivial]
    ring
  rw [heq]
  calc
    _ ≤ ‖⟪v, w⟫_ℝ‖ + ‖⟪Poincare.EuclideanSpace.euclideanTail v,
        Poincare.EuclideanSpace.euclideanTail w⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := by
      exact add_le_add (norm_inner_le_norm v w)
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul (cylinder_tail_norm_le v) (cylinder_tail_norm_le w)
            (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

theorem roundCylinderEuclideanCoefficients_inverse_norm_zero_le :
    ‖(roundCylinderEuclideanCoefficients 0).inverse‖ ≤ 1 := by
  simpa using CoordinateExponential.norm_inverse_le_of_ellipticity
    (B := roundCylinderEuclideanCoefficients 0) (a := 1) zero_lt_one
    (fun v => by simpa using roundCylinderEuclideanMetric_norm_sq_le v)

theorem roundCylinderEuclideanCoefficients_perturbation_lower
    {B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    (hB : ‖B - roundCylinderEuclideanCoefficients 0‖ ≤ 1 / 2)
    (v : EuclideanSpace ℝ (Fin 3)) : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v := by
  have herr := (B - roundCylinderEuclideanCoefficients 0).le_opNorm₂ v v
  have hnorm := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖v‖)
  have hmodel := roundCylinderEuclideanMetric_norm_sq_le v
  change ‖v‖ ^ 2 ≤ roundCylinderEuclideanCoefficients 0 v v at hmodel
  simp only [sub_apply, Real.norm_eq_abs] at herr
  have hlow := neg_abs_le (B v v - roundCylinderEuclideanCoefficients 0 v v)
  nlinarith

theorem roundCylinderEuclideanCoefficients_perturbation_inverse_norm_le
    {B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    (hB : ‖B - roundCylinderEuclideanCoefficients 0‖ ≤ 1 / 2) :
    ‖B.inverse‖ ≤ 2 := by
  simpa using CoordinateExponential.norm_inverse_le_of_ellipticity
    (a := (1 / 2 : ℝ)) (by norm_num)
    (roundCylinderEuclideanCoefficients_perturbation_lower hB)

theorem roundCylinderEuclideanCoefficients_perturbation_inverse_sub_norm_le
    {B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    (hB : ‖B - roundCylinderEuclideanCoefficients 0‖ ≤ 1 / 2) :
    ‖B.inverse - (roundCylinderEuclideanCoefficients 0).inverse‖ ≤
      2 * ‖B - roundCylinderEuclideanCoefficients 0‖ := by
  let C := roundCylinderEuclideanCoefficients 0
  have hiB := CoordinateTransition.isInvertible_of_uniformEllipticity
    (a := (1 / 2 : ℝ)) (by norm_num)
    (roundCylinderEuclideanCoefficients_perturbation_lower hB)
  have hiC : C.IsInvertible := CoordinateTransition.isInvertible_of_uniformEllipticity
    (a := (1 : ℝ)) zero_lt_one
    (fun v => by simpa [C] using roundCylinderEuclideanMetric_norm_sq_le v)
  have hnB := roundCylinderEuclideanCoefficients_perturbation_inverse_norm_le hB
  have hnC : ‖C.inverse‖ ≤ 1 := roundCylinderEuclideanCoefficients_inverse_norm_zero_le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  change ‖B.inverse ξ - C.inverse ξ‖ ≤ _
  rw [CoordinateExponential.inverse_sub_inverse_apply hiB hiC]
  calc
    _ ≤ ‖B.inverse‖ * ‖(C - B) (C.inverse ξ)‖ := B.inverse.le_opNorm _
    _ ≤ 2 * (‖C - B‖ * (1 * ‖ξ‖)) := by
      apply mul_le_mul hnB _ (norm_nonneg _) (by norm_num)
      exact ((C - B).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left
          ((C.inverse.le_opNorm ξ).trans
            (mul_le_mul_of_nonneg_right hnC (norm_nonneg ξ))) (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev C B]; dsimp only [C]; ring

end PoincareConjecture
