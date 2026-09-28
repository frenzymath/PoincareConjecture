import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_EvolvingCylinderCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "H" => cylinderHorizontalForm
local notation "Z" => cylinderHeightCovector

noncomputable local instance modelCylinderCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelCylinderCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable def modelCylinderDenominator (x : E) : ℝ :=
  ‖(cylinderEuclideanEquiv x).1‖ ^ 2 + 4

theorem modelCylinderDenominator_pos (x : E) : 0 < modelCylinderDenominator x := by
  unfold modelCylinderDenominator
  positivity

theorem modelCylinderDenominator_hasFDerivAt (x : E) :
    HasFDerivAt modelCylinderDenominator (2 • H x) x := by
  have h := (((hasStrictFDerivAt_norm_sq (cylinderHorizontalProjection x)).hasFDerivAt.comp x
    cylinderHorizontalProjection.hasFDerivAt).add_const 4)
  convert! h using 1

theorem model_evolvingCylinderField (t : ℝ) (x : E) :
    evolvingCylinderModelField t x =
      (32 * (1 - t) / modelCylinderDenominator x ^ 2) • H +
        cylinderHeightCovector.smulRight cylinderHeightCovector := by
  unfold evolvingCylinderModelField cylinderModelField cylinderSphereFactor
  dsimp only [modelCylinderDenominator]
  module

theorem model_evolvingCylinderField_apply (t : ℝ) (x u v : E) :
    evolvingCylinderModelField t x u v =
      (32 * (1 - t) / modelCylinderDenominator x ^ 2) * H u v + Z u * Z v := by
  rw [model_evolvingCylinderField]
  rfl

theorem model_evolvingCylinderField_first (t : ℝ) (x v a b : E) :
    fderiv ℝ (evolvingCylinderModelField t) x v a b =
      (-128 * (1 - t) / modelCylinderDenominator x ^ 3) * H x v * H a b := by
  rw [evolvingCylinderModelField_fderiv]
  simp only [smul_apply, smul_eq_mul, cylinderModelField_fderiv, modelCylinderDenominator]
  ring

theorem modelCylinderDerivativeFactor_hasFDerivAt (t : ℝ) (x : E) :
    HasFDerivAt (fun p => -128 * (1 - t) / modelCylinderDenominator p ^ 3)
      ((768 * (1 - t) / modelCylinderDenominator x ^ 4) • H x) x := by
  have hne := (modelCylinderDenominator_pos x).ne'
  have h := (((hasFDerivAt_inv (pow_ne_zero 3 hne)).comp x
    ((modelCylinderDenominator_hasFDerivAt x).pow 3)).const_smul (-128 * (1 - t)))
  change HasFDerivAt (fun p => (-128 * (1 - t)) * (modelCylinderDenominator p ^ 3)⁻¹) _ x at h
  simp only [div_eq_mul_inv]
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  field_simp [hne]
  ring

set_option maxHeartbeats 800000 in

theorem model_evolvingCylinderField_second (t : ℝ) (x u v a b : E) :
    fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x u v a b =
      (768 * (1 - t) / modelCylinderDenominator x ^ 4) * H x u * H x v * H a b +
        (-128 * (1 - t) / modelCylinderDenominator x ^ 3) * H u v * H a b := by
  rw [← second_fderiv_bilinear_component (evolvingCylinderModelField_contDiff t).contDiffAt]
  simp only [fderiv_bilinear_component
    ((evolvingCylinderModelField_contDiff t).differentiable (by simp) _),
    model_evolvingCylinderField_first]
  have h := (((modelCylinderDerivativeFactor_hasFDerivAt t x).mul
    (cylinderHorizontalForm.flip v).hasFDerivAt).mul_const (H a b)).fderiv
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L u) h
  simpa only [Pi.mul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, add_apply, smul_eq_mul, mul_add, mul_assoc, mul_comm,
    mul_left_comm, add_comm] using hv

theorem model_horizontal_symm (u v : E) : H u v = H v u := by
  rw [cylinderHorizontalForm_apply, cylinderHorizontalForm_apply, real_inner_comm]

@[simp] theorem model_horizontal_vertical_left (v : E) : H (e 2) v = 0 := by
  rw [cylinderHorizontalForm_apply, cylinderEuclideanEquiv_basis]
  simp [roundCylinderCoordinateBasis]

@[simp] theorem model_horizontal_vertical_right (v : E) : H v (e 2) = 0 := by
  rw [model_horizontal_symm, model_horizontal_vertical_left]

noncomputable def modelHorizontalVector (v : E) : E := v - Z v • e 2

@[simp] theorem model_horizontalVector_left (u v : E) :
    H (modelHorizontalVector u) v = H u v := by
  simp only [modelHorizontalVector, map_sub, map_smul, sub_apply, smul_apply,
    smul_eq_mul, model_horizontal_vertical_left, mul_zero, sub_zero]

@[simp] theorem model_horizontalVector_right (u v : E) :
    H u (modelHorizontalVector v) = H u v := by
  simp only [modelHorizontalVector, map_sub, map_smul, smul_eq_mul,
    model_horizontal_vertical_right, mul_zero, sub_zero]

@[simp] theorem model_horizontalVector_height (v : E) : Z (modelHorizontalVector v) = 0 := by
  simp only [modelHorizontalVector, map_sub, map_smul, smul_eq_mul]
  rw [cylinderHeightCovector_basis]
  simp [roundCylinderCoordinateBasis]

theorem model_evolvingCylinderField_isInvertible {t : ℝ} (ht : t < 1) (x : E) :
    (evolvingCylinderModelField t x).IsInvertible := by
  let a := 32 * (1 - t) / modelCylinderDenominator x ^ 2
  have ha : 0 < a := div_pos (mul_pos (by norm_num) (sub_pos.mpr ht))
    (pow_pos (modelCylinderDenominator_pos x) 2)
  apply CoordinateTransition.isInvertible_of_uniformEllipticity (lt_min ha zero_lt_one)
  intro v
  have hsplit := congrArg (fun A : MetricCoefficient 3 => A v v)
    cylinderHorizontalForm_add_vertical
  change H v v + Z v * Z v = inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ H v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hV : 0 ≤ Z v * Z v := mul_self_nonneg _
  have h1 := mul_le_mul_of_nonneg_right (min_le_left a 1) hH
  have h2 := mul_le_mul_of_nonneg_right (min_le_right a 1) hV
  rw [model_evolvingCylinderField]
  change min a 1 * ‖v‖ ^ 2 ≤ a * H v v + Z v * Z v
  rw [← hsplit, mul_add]
  exact add_le_add h1 (by simpa only [one_mul] using h2)

theorem model_evolvingCylinder_christoffel {t : ℝ} (ht : t < 1) (x u v : E) :
    jetChristoffel (metricTwoJet (evolvingCylinderModelField t) x) u v =
      (-2 / modelCylinderDenominator x) •
        (H x u • modelHorizontalVector v + H x v • modelHorizontalVector u -
          H u v • modelHorizontalVector x) := by
  let w := (-2 / modelCylinderDenominator x) •
    (H x u • modelHorizontalVector v + H x v • modelHorizontalVector u -
      H u v • modelHorizontalVector x)
  have heq : evolvingCylinderModelField t x w =
      metricKoszulCovector (fderiv ℝ (evolvingCylinderModelField t) x) u v := by
    apply ContinuousLinearMap.ext
    intro z
    rw [model_evolvingCylinderField]
    simp only [metricKoszulCovector, ContinuousLinearMap.flip_apply, smul_apply,
      add_apply, sub_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
      model_evolvingCylinderField_first]
    dsimp only [w]
    simp only [map_smul, map_add, map_sub, smul_apply, add_apply, sub_apply,
      smul_eq_mul, model_horizontalVector_right, model_horizontalVector_height,
      mul_zero, add_zero, sub_zero, model_horizontal_symm]
    ring
  change (evolvingCylinderModelField t x).inverse
    (metricKoszulCovector (fderiv ℝ (evolvingCylinderModelField t) x) u v) = w
  rw [← heq, (model_evolvingCylinderField_isInvertible ht x).inverse_apply_self]

theorem model_evolvingCylinder_christoffel_horizontal {t : ℝ} (ht : t < 1)
    (x u v w : E) :
    H (jetChristoffel (metricTwoJet (evolvingCylinderModelField t) x) u v) w =
      (-2 / modelCylinderDenominator x) *
        (H x u * H v w + H x v * H u w - H u v * H x w) := by
  rw [model_evolvingCylinder_christoffel ht]
  simp only [map_smul, map_add, map_sub, smul_apply, add_apply, sub_apply,
    smul_eq_mul, model_horizontalVector_left]

theorem model_evolvingCylinder_christoffel_horizontal_right {t : ℝ} (ht : t < 1)
    (x u v w : E) :
    H w (jetChristoffel (metricTwoJet (evolvingCylinderModelField t) x) u v) =
      (-2 / modelCylinderDenominator x) *
        (H x u * H v w + H x v * H u w - H u v * H x w) := by
  rw [model_horizontal_symm, model_evolvingCylinder_christoffel_horizontal ht]

theorem model_evolvingCylinder_christoffel_height {t : ℝ} (ht : t < 1) (x u v : E) :
    Z (jetChristoffel (metricTwoJet (evolvingCylinderModelField t) x) u v) = 0 := by
  rw [model_evolvingCylinder_christoffel ht]
  simp only [map_smul, map_add, map_sub, smul_eq_mul, model_horizontalVector_height,
    mul_zero, add_zero, sub_zero]

noncomputable def modelCylinderInverseWeight (t : ℝ) (x : E) : Fin 3 → ℝ :=
  ![(32 * (1 - t) / modelCylinderDenominator x ^ 2)⁻¹,
    (32 * (1 - t) / modelCylinderDenominator x ^ 2)⁻¹, 1]

theorem model_evolvingCylinder_inverse_proj {t : ℝ} (ht : t < 1) (x : E) (i : Fin 3) :
    (evolvingCylinderModelField t x).inverse (EuclideanSpace.proj i) =
      modelCylinderInverseWeight t x i • e i := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hden : modelCylinderDenominator x ≠ 0 := (modelCylinderDenominator_pos x).ne'
  have heq : evolvingCylinderModelField t x
      (modelCylinderInverseWeight t x i • e i) = EuclideanSpace.proj i := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro j
    change evolvingCylinderModelField t x (modelCylinderInverseWeight t x i • e i) (e j) = _
    rw [model_evolvingCylinderField_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [cylinderHorizontalForm_basis, cylinderHeightCovector_basis, cylinderHeightCovector_basis]
    fin_cases i <;> fin_cases j <;>
      simp [modelCylinderInverseWeight, cylinderHorizontalGram, roundCylinderCoordinateBasis,
        EuclideanSpace.inner_single_left, PiLp.proj_apply, htime, hden]
  rw [← heq, (model_evolvingCylinderField_isInvertible ht x).inverse_apply_self]

end PoincareConjecture.M45
