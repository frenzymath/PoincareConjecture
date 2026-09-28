import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNormal
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderContractions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)


noncomputable def neckModelFrame : E ≃L[ℝ] E :=
  M35.cylinderCoordinateEquiv.trans
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E2)
      (Units.mk0 (Real.sqrt 2)⁻¹ (by positivity))).prodCongr
        (ContinuousLinearEquiv.refl ℝ ℝ)).trans M35.cylinderCoordinateEquiv.symm)

theorem neckModelFrame_coordinate (v : E) :
    M35.cylinderCoordinateEquiv (neckModelFrame v) =
      ((Real.sqrt 2)⁻¹ • (M35.cylinderCoordinateEquiv v).1,
        (M35.cylinderCoordinateEquiv v).2) := by
  simp [neckModelFrame, ContinuousLinearEquiv.smulLeft]

theorem neckModelFrame_basis (i : Fin 3) :
    neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      (if i = 2 then 1 else (Real.sqrt 2)⁻¹) •
        EuclideanSpace.basisFun (Fin 3) ℝ i := by
  apply M35.cylinderCoordinateEquiv.injective
  rw [neckModelFrame_coordinate, map_smul, M35.cylinderCoordinateEquiv_basis]
  fin_cases i <;> simp [roundCylinderCoordinateBasis]

private theorem inverse_sqrt_two_square : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num


theorem neckModelFrame_isometry (s : ℝ) (v w : E) :
    (M35.cylinderEuclideanMetric 0 (by norm_num)).inner
      (M35.cylinderCoordinateEquiv.symm (0, s))
      (neckModelFrame v) (neckModelFrame w) = inner ℝ v w := by
  have hsplit : inner ℝ (M35.cylinderCoordinateEquiv v).1
      (M35.cylinderCoordinateEquiv w).1 +
        (M35.cylinderCoordinateEquiv v).2 * (M35.cylinderCoordinateEquiv w).2 =
      inner ℝ v w := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      M35.cylinderCoordinateEquiv_fst, M35.cylinderCoordinateEquiv_snd,
      RCLike.inner_apply, conj_trivial]
    change w 0 * v 0 + w 1 * v 1 + v 2 * w 2 =
      w 0 * v 0 + w 1 * v 1 + w 2 * v 2
    ring
  change M35.cylinderEuclideanCoefficients 0
    (M35.cylinderCoordinateEquiv.symm (0, s)) (neckModelFrame v) (neckModelFrame w) = _
  rw [M35.cylinderEuclideanCoefficients_apply,
    ContinuousLinearEquiv.apply_symm_apply, neckModelFrame_coordinate,
    neckModelFrame_coordinate]
  simp only [norm_zero, zero_pow (by omega : 2 ≠ 0), zero_add,
    real_inner_smul_left, real_inner_smul_right]
  norm_num
  calc
    _ = (2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹)) *
        inner ℝ (M35.cylinderCoordinateEquiv v).1 (M35.cylinderCoordinateEquiv w).1 +
        (M35.cylinderCoordinateEquiv v).2 * (M35.cylinderCoordinateEquiv w).2 := by ring
    _ = _ := by rw [inverse_sqrt_two_square]; norm_num; exact hsplit


theorem neckModelFrame_ricci
    (D : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num)))
    (q : UnitTwoSphere) (s : ℝ) :
    D.ricci (M35.cylinderCoordinateEquiv.symm (0, s))
      (neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 0))
      (neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 0)) = 1 / 2 ∧
    D.ricci (M35.cylinderCoordinateEquiv.symm (0, s))
      (neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 2))
      (neckModelFrame (EuclideanSpace.basisFun (Fin 3) ℝ 2)) = 0 := by
  let p := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  have hang : D.ricci p (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0) = 1 := by
    convert M35.cylinder_ricci_center 0 zero_lt_one D q s 0 0 using 1
    norm_num [roundCylinderCoordinateBasis, Matrix.cons_val_zero]
  have haxis : D.ricci p (EuclideanSpace.basisFun (Fin 3) ℝ 2)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2) = 0 := by
    convert M35.cylinder_ricci_center 0 zero_lt_one D q s 2 2 using 1
    norm_num [roundCylinderCoordinateBasis, Matrix.cons_val_two]
  constructor
  · rw [neckModelFrame_basis]
    norm_num only [Fin.reduceEq, if_false]
    change (M13.ricciLinear D p) ((Real.sqrt 2)⁻¹ • _) ((Real.sqrt 2)⁻¹ • _) = _
    simp only [map_smul, smul_eq_mul]
    change (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * D.ricci p _ _) = _
    rw [hang, mul_one, inverse_sqrt_two_square]
  · rw [neckModelFrame_basis]
    norm_num only [Fin.reduceEq, if_true, one_smul]
    exact haxis

end PoincareConjecture.Proofs.M47
