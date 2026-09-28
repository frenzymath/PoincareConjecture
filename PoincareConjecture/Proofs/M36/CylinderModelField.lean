import PoincareConjecture.Proofs.M36.CylinderCoefficientField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem euclideanThree_bilinear_ext
    {A B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ}
    (h : ∀ i j : Fin 3,
      A (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) :
    A = B := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  exact h i

noncomputable def cylinderHorizontalProjection : E₃ →L[ℝ] E₂ :=
  (ContinuousLinearMap.fst ℝ E₂ ℝ).comp cylinderEuclideanEquiv.toContinuousLinearMap

noncomputable def cylinderHeightCovector : E₃ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ E₂ ℝ).comp cylinderEuclideanEquiv.toContinuousLinearMap

noncomputable def cylinderHorizontalForm : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  (cylinderHorizontalProjection.precomp ℝ).comp
    ((innerSL ℝ).comp cylinderHorizontalProjection)

theorem cylinderHorizontalForm_apply (u v : E₃) :
    cylinderHorizontalForm u v =
      inner ℝ (cylinderEuclideanEquiv u).1 (cylinderEuclideanEquiv v).1 := rfl

theorem cylinderHorizontalForm_basis (i j : Fin 3) :
    cylinderHorizontalForm (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) = cylinderHorizontalGram i j := by
  simp only [cylinderHorizontalForm_apply, cylinderEuclideanEquiv_basis,
    cylinderHorizontalGram]

theorem cylinderHeightCovector_basis (i : Fin 3) :
    cylinderHeightCovector (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      (roundCylinderCoordinateBasis i).2 := by
  change (cylinderEuclideanEquiv (EuclideanSpace.basisFun (Fin 3) ℝ i)).2 = _
  rw [cylinderEuclideanEquiv_basis]

theorem cylinderHorizontalForm_add_vertical :
    cylinderHorizontalForm + cylinderHeightCovector.smulRight cylinderHeightCovector =
      innerSL ℝ := by
  apply euclideanThree_bilinear_ext
  intro i j
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    cylinderHorizontalForm_basis, cylinderHeightCovector_basis]
  change cylinderHorizontalGram i j +
    (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 =
      inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  rw [(EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite]
  fin_cases i <;> fin_cases j <;>
    simp [cylinderHorizontalGram, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]

noncomputable def cylinderModelField (p : E₃) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  cylinderSphereFactor (cylinderEuclideanEquiv p) • cylinderHorizontalForm +
    cylinderHeightCovector.smulRight cylinderHeightCovector

theorem cylinderModelField_contDiff : ContDiff ℝ ∞ cylinderModelField :=
  ((cylinderSphereFactor_contDiff.comp cylinderEuclideanEquiv.contDiff).smul
    contDiff_const).add contDiff_const

theorem centeredCylinderBilinear_gram (theta : UnitTwoSphere) (s : ℝ) :
    centeredCylinderBilinear (roundCylinderGram 0 (chartAt E₂ theta)) s =
      cylinderModelField := by
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderBilinear_basis, roundCylinderGram_chart_entry]
  simp only [cylinderModelField, add_apply, smul_apply, smul_eq_mul,
    cylinderHorizontalForm_basis, ContinuousLinearMap.smulRight_apply,
    cylinderHeightCovector_basis]
  simp [cylinderSphereFactor]

theorem cylinderModelField_zero :
    cylinderModelField 0 = (2 : ℝ) • cylinderHorizontalForm +
      cylinderHeightCovector.smulRight cylinderHeightCovector := by
  norm_num [cylinderModelField, cylinderSphereFactor]

theorem cylinderModelField_zero_lower (v : E₃) :
    ‖v‖ ^ 2 ≤ cylinderModelField 0 v v := by
  have hsplit := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul] at hsplit
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  rw [cylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  linarith

theorem cylinderModelField_fderiv (p v a b : E₃) :
    fderiv ℝ cylinderModelField p v a b =
      (-128 / (‖(cylinderEuclideanEquiv p).1‖ ^ 2 + 4) ^ 3) *
        cylinderHorizontalForm p v * cylinderHorizontalForm a b := by
  have hd := (((cylinderSphereFactor_hasFDerivAt (cylinderEuclideanEquiv p)).comp p
    cylinderEuclideanEquiv.hasFDerivAt).smul_const cylinderHorizontalForm).add_const
      (cylinderHeightCovector.smulRight cylinderHeightCovector)
  have he := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v a b) hd.fderiv
  change fderiv ℝ (fun y => cylinderSphereFactor (cylinderEuclideanEquiv y) •
    cylinderHorizontalForm + cylinderHeightCovector.smulRight cylinderHeightCovector) p v a b = _
  simpa [cylinderModelField, cylinderHorizontalForm_apply, smul_eq_mul,
    mul_assoc] using he

theorem cylinderModelField_fderiv_zero : fderiv ℝ cylinderModelField 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  simp [cylinderModelField_fderiv]

set_option maxHeartbeats 800000 in

theorem cylinderModelField_second_fderiv_zero (u v a b : E₃) :
    fderiv ℝ (fderiv ℝ cylinderModelField) 0 u v a b =
      -2 * cylinderHorizontalForm u v * cylinderHorizontalForm a b := by
  rw [← second_fderiv_bilinear_component cylinderModelField_contDiff.contDiffAt]
  simp only [fderiv_bilinear_component (cylinderModelField_contDiff.differentiable
    (by simp) _), cylinderModelField_fderiv]
  let t : E₃ → ℝ := fun p => -128 / (‖(cylinderEuclideanEquiv p).1‖ ^ 2 + 4) ^ 3
  have ht : ContDiff ℝ ∞ t := by
    apply contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp
        (contDiff_fst.comp cylinderEuclideanEquiv.contDiff)).add contDiff_const).pow 3)
    intro p
    exact pow_ne_zero 3 (ne_of_gt
      (show 0 < ‖(cylinderEuclideanEquiv p).1‖ ^ 2 + 4 by positivity))
  have hd := (((ht.differentiable (by simp) 0).hasFDerivAt.mul
    (cylinderHorizontalForm.flip v).hasFDerivAt).mul_const
      (cylinderHorizontalForm a b)).fderiv
  have he := congrArg (fun A : E₃ →L[ℝ] ℝ => A u) hd
  simpa [t, show (-128 / 4 ^ 3 : ℝ) = -2 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using he

noncomputable def centeredCylinderMetric
    (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (s : ℝ) :
    E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  centeredCylinderBilinear (roundCylinderTensorCoefficient B (chartAt E₂ theta)) s

theorem centeredCylinderMetric_sub_model
    (B : RoundCylinderTwoTensor) (theta : UnitTwoSphere) (s : ℝ) :
    (fun p => centeredCylinderMetric B theta s p - cylinderModelField p) =
      centeredCylinderError B theta s := by
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  rw [← centeredCylinderBilinear_gram theta s]
  simp only [centeredCylinderMetric, centeredCylinderError, sub_apply,
    centeredCylinderBilinear_basis]

theorem centeredCylinderMetric_contDiffAt {epsilon : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (centeredCylinderMetric B z.1 z.2) 0 := by
  have he : centeredCylinderMetric B z.1 z.2 =
      fun p => centeredCylinderError B z.1 z.2 p + cylinderModelField p := by
    funext p
    have h := congrFun (centeredCylinderMetric_sub_model B z.1 z.2) p
    exact sub_eq_iff_eq_add.mp h
  rw [he]
  exact (centeredCylinderError_contDiffAt hB z hz).add cylinderModelField_contDiff.contDiffAt

end PoincareConjecture.M36
