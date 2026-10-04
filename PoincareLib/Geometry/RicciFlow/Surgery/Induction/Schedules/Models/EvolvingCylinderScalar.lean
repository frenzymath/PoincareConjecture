import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.EvolvingCylinderCurvature
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.ScalarJetConstancy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.RicciJetNorm

/-!
# The spatially constant scalar field of the evolving cylinder

The actual stereographic metric has scalar curvature `(1-t)⁻¹` at every
point. Its native four-jet scalar Laplacian is therefore zero. The Ricci
tensor is retained as the time-independent horizontal sphere metric.
Source: Morgan--Tian Proposition 15.2, pp. 353-354, and equation (3.7), p. 41.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Native curvature and scalar operators use nested metric-jet spaces.
set_option maxSynthPendingDepth 16

open scoped ContDiff Topology BigOperators

open PoincareMT.MetricSurgery

namespace PoincareMT.M45

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
-- The fixed three-dimensional inverse-metric contraction has nine components.
/-- The native Ricci tensor on every coordinate basis pair.
Source: the limiting cylinder in Proposition 15.2, pp. 353-354. -/
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

/-- The native Ricci tensor equals half the static horizontal metric,
independently of model time. Source: Proposition 15.2, pp. 353-354. -/
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

/-- The literal scalar two-jet field is constant at every spatial point.
Source: the evolving round cylinder in Proposition 15.2, pp. 353-354. -/
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

/-- The actual evolving model has zero spatial scalar Laplacian.
This supplies the strict scalar-evolution neighborhood used by gluing.
Source: Proposition 15.2, pp. 353-354, and equation (3.7), p. 41. -/
theorem model_evolvingCylinder_scalarLaplacian {t : ℝ} (ht : t < 1) (x : E) :
    jetScalarLaplacian (scalarMetricFourJet (evolvingCylinderModelField t) x) = 0 := by
  apply model_jetScalarLaplacian_eq_zero_of_const _ _
    (evolvingCylinderModelField_contDiff t).contDiffAt
    (model_evolvingCylinderField_isInvertible ht x) ((1 - t)⁻¹)
  funext y
  exact model_evolvingCylinder_scalar ht y

end PoincareMT.M45
