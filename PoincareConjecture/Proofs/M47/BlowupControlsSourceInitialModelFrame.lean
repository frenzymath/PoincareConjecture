import PoincareConjecture.Proofs.M47.BlowupControlsCapModelNormal
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderContractions









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)


noncomputable def sourceInitialModelFrame (u : ℝ) (hu : u < 1) : E ≃L[ℝ] E :=
  M35.cylinderCoordinateEquiv.trans
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E2)
      (Units.mk0 (Real.sqrt (2 * (1 - u)))⁻¹
        (by
          have h : 0 < 2 * (1 - u) := by linarith only [hu]
          exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr h))))).prodCongr
          (ContinuousLinearEquiv.refl ℝ ℝ)).trans M35.cylinderCoordinateEquiv.symm)

theorem sourceInitialModelFrame_coordinate (u : ℝ) (hu : u < 1) (v : E) :
    M35.cylinderCoordinateEquiv (sourceInitialModelFrame u hu v) =
      ((Real.sqrt (2 * (1 - u)))⁻¹ • (M35.cylinderCoordinateEquiv v).1,
        (M35.cylinderCoordinateEquiv v).2) := by
  simp only [sourceInitialModelFrame, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply]
  rfl


theorem sourceInitialModelFrame_axial (u : ℝ) (hu : u < 1) :
    sourceInitialModelFrame u hu (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  apply M35.cylinderCoordinateEquiv.injective
  rw [sourceInitialModelFrame_coordinate, M35.cylinderCoordinateEquiv_basis]
  simp [roundCylinderCoordinateBasis]


theorem sourceInitialModelFrame_isometry (u : ℝ) (hu : u < 1)
    (s : ℝ) (v w : E) :
    (M35.cylinderEuclideanMetric u hu).inner
      (M35.cylinderCoordinateEquiv.symm (0, s))
      (sourceInitialModelFrame u hu v) (sourceInitialModelFrame u hu w) = inner ℝ v w := by
  have hfactor : 0 < 2 * (1 - u) := by linarith only [hu]
  have hcancel : (2 * (1 - u)) *
      ((Real.sqrt (2 * (1 - u)))⁻¹ * (Real.sqrt (2 * (1 - u)))⁻¹) = 1 := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt hfactor.le, mul_inv_cancel₀ hfactor.ne']
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
  change M35.cylinderEuclideanCoefficients u
    (M35.cylinderCoordinateEquiv.symm (0, s))
      (sourceInitialModelFrame u hu v) (sourceInitialModelFrame u hu w) = _
  rw [M35.cylinderEuclideanCoefficients_apply, ContinuousLinearEquiv.apply_symm_apply,
    sourceInitialModelFrame_coordinate, sourceInitialModelFrame_coordinate]
  simp only [norm_zero, zero_pow (by omega : 2 ≠ 0), zero_add,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = ((2 * (1 - u)) *
        ((Real.sqrt (2 * (1 - u)))⁻¹ * (Real.sqrt (2 * (1 - u)))⁻¹)) *
        inner ℝ (M35.cylinderCoordinateEquiv v).1 (M35.cylinderCoordinateEquiv w).1 +
        (M35.cylinderCoordinateEquiv v).2 * (M35.cylinderCoordinateEquiv w).2 := by ring
    _ = _ := by rw [hcancel, one_mul]; exact hsplit


theorem sourceInitialModelFrame_axial_ricci (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (M35.cylinderEuclideanMetric u hu))
    (q : UnitTwoSphere) (s : ℝ) :
    D.ricci (M35.cylinderCoordinateEquiv.symm (0, s))
      (sourceInitialModelFrame u hu (EuclideanSpace.basisFun (Fin 3) ℝ 2))
      (sourceInitialModelFrame u hu (EuclideanSpace.basisFun (Fin 3) ℝ 2)) = 0 := by
  rw [sourceInitialModelFrame_axial]
  convert M35.cylinder_ricci_center u hu D q s 2 2 using 1
  norm_num [roundCylinderCoordinateBasis, Matrix.cons_val_two]

end PoincareConjecture.M47
