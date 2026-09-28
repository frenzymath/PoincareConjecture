import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNative








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem cap_model_ricciNorm_sq (u : ℝ) (hu : u < 1)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) (s : ℝ) :
    ((M35.cylinderEuclideanMetric u hu).tensorNorm D0.ricciEvaluation
      (M35.cylinderCoordinateEquiv.symm (0, s))) ^ 2 =
      2 * ((2 * (1 - u))⁻¹) ^ 2 := by
  rw [cap_model_tensorNorm_sq u hu q s _
    ((M04.isSmoothCovariantTensor_ricciEvaluation D0).1 _),
    M35.roundCylinderTensorNormSquared_center hu]
  let f : (Fin 2 → Fin 3) → ℝ := fun a =>
    (∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i)) *
      (D0.ricciEvaluation (M35.cylinderCoordinateEquiv.symm (0, s))
        (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) ^ 2
  change (∑ a : Fin 2 → Fin 3, f a) = _
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp f, Fintype.sum_prod_type]
  change (∑ i : Fin 3, ∑ j : Fin 3,
    (∏ k : Fin 2, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (![i, j] k)) *
      (D0.ricci (M35.cylinderCoordinateEquiv.symm (0, s))
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) ^ 2) = _
  simp_rw [M35.cylinder_ricci_center u hu D0 q]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, roundCylinderCoordinateBasis,
    EuclideanSpace.inner_single_left]
  ring



theorem cap_model_ricciNorm_le (u : ℝ) (hu : u ≤ 0)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric u (by linarith)))
    (q : UnitTwoSphere) (s : ℝ) :
    (M35.cylinderEuclideanMetric u (by linarith)).tensorNorm D0.ricciEvaluation
      (M35.cylinderCoordinateEquiv.symm (0, s)) ≤ (71 / 100 : ℝ) := by
  have hd : (2 : ℝ) ≤ 2 * (1 - u) := by linarith
  have hp : 0 < 2 * (1 - u) := by linarith
  have hi0 : 0 ≤ (2 * (1 - u))⁻¹ := (inv_pos.mpr hp).le
  have hi : (2 * (1 - u))⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hp (by norm_num)]
    linarith
  have hsq := cap_model_ricciNorm_sq u (by linarith) D0 q s
  nlinarith only [hsq, hi, hi0]

end PoincareConjecture.M47
