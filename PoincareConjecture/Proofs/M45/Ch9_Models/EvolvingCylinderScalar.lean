import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderCurvature
import PoincareConjecture.Proofs.M45.Ch9_Models.ScalarJetConstancy
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RicciJetNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "H" => cylinderHorizontalForm

noncomputable local instance modelScalarCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelScalarCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance modelScalarTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance modelScalarTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

set_option maxHeartbeats 800000 in

theorem model_evolvingCylinder_ricci_basis {t : ℝ} (ht : t < 1)
    (x : E) (i j : Fin 3) :
    jetRicci (metricTwoJet (evolvingCylinderModelField t) x) (e i) (e j) =
      (16 / modelCylinderDenominator x ^ 2) * H (e i) (e j) := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hden : modelCylinderDenominator x ≠ 0 := (modelCylinderDenominator_pos x).ne'
  change (∑ k, ∑ l,
    EuclideanSpace.proj l ((evolvingCylinderModelField t x).inverse (EuclideanSpace.proj k)) *
      jetCurvature (metricTwoJet (evolvingCylinderModelField t) x) (e i) (e k) (e j) (e l)) = _
  simp only [model_evolvingCylinder_inverse_proj ht,
    model_evolvingCylinder_curvature_basis ht, cylinderHorizontalForm_basis]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, modelCylinderInverseWeight,
      cylinderHorizontalGram, roundCylinderCoordinateBasis,
      EuclideanSpace.inner_single_left, PiLp.proj_apply] <;>
    field_simp [htime, hden] <;> ring

theorem model_evolvingCylinder_ricciBilinear {t : ℝ} (ht : t < 1) (x : E) :
    jetRicciBilinear (metricTwoJet (evolvingCylinderModelField t) x) =
      (1 / 2 : ℝ) •
        (cylinderModelField x - cylinderHeightCovector.smulRight cylinderHeightCovector) := by
  apply euclideanThree_bilinear_ext
  intro i j
  have heval : jetRicciBilinear (metricTwoJet (evolvingCylinderModelField t) x)
      (e i) (e j) = jetRicci (metricTwoJet (evolvingCylinderModelField t) x) (e i) (e j) := by
    simp only [jetRicciBilinear, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, smul_eq_mul,
      (EuclideanSpace.basisFun (Fin 3) ℝ).inner_eq_ite]
    simp
  rw [heval, model_evolvingCylinder_ricci_basis ht, cylinderModelField]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    cylinderSphereFactor, modelCylinderDenominator]
  ring

theorem model_evolvingCylinder_scalar {t : ℝ} (ht : t < 1) (x : E) :
    jetScalarCurvature (metricTwoJet (evolvingCylinderModelField t) x) = (1 - t)⁻¹ := by
  have htime : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hden : modelCylinderDenominator x ≠ 0 := (modelCylinderDenominator_pos x).ne'
  change (∑ i, ∑ j,
    EuclideanSpace.proj j ((evolvingCylinderModelField t x).inverse (EuclideanSpace.proj i)) *
      jetRicci (metricTwoJet (evolvingCylinderModelField t) x) (e i) (e j)) = _
  simp only [model_evolvingCylinder_inverse_proj ht,
    model_evolvingCylinder_ricci_basis ht, cylinderHorizontalForm_basis]
  simp [Fin.sum_univ_three, modelCylinderInverseWeight,
    cylinderHorizontalGram, roundCylinderCoordinateBasis,
    PiLp.proj_apply]
  field_simp [htime, hden]
  ring

theorem model_evolvingCylinder_scalarLaplacian {t : ℝ} (ht : t < 1) (x : E) :
    jetScalarLaplacian (scalarMetricFourJet (evolvingCylinderModelField t) x) = 0 := by
  apply model_jetScalarLaplacian_eq_zero_of_const _ _
    (evolvingCylinderModelField_contDiff t).contDiffAt
    (model_evolvingCylinderField_isInvertible ht x) ((1 - t)⁻¹)
  funext y
  exact model_evolvingCylinder_scalar ht y

end PoincareConjecture.M45
