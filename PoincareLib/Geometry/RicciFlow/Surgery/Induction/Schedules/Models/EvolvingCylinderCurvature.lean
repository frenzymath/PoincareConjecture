import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.EvolvingCylinderCoefficients

/-!
# Curvature of the evolving cylinder in stereographic coordinates

This is the actual native curvature contraction of the checked metric
derivatives and connection. Source: Morgan--Tian Proposition 15.2,
pp. 353-354.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Native curvature evaluations contain four nested metric coefficient slots.
set_option maxSynthPendingDepth 16

open scoped ContDiff Topology BigOperators

open PoincareMT.MetricSurgery

namespace PoincareMT.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "H" => cylinderHorizontalForm

noncomputable local instance modelCurvatureCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelCurvatureCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

/-- Coordinate components of the cylinder's horizontal form.
Source: the product-cylinder model in Proposition 15.2, pp. 353-354. -/
theorem model_horizontal_basis_left (i : Fin 3) (x : E) :
    H (e i) x = ![(cylinderEuclideanEquiv x).1 0,
      (cylinderEuclideanEquiv x).1 1, 0] i := by
  rw [cylinderHorizontalForm_apply, cylinderEuclideanEquiv_basis]
  fin_cases i <;> simp [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left]

/-- The horizontal form's coordinate components in the second slot.
Source: Proposition 15.2, pp. 353-354. -/
theorem model_horizontal_basis_right (x : E) (i : Fin 3) :
    H x (e i) = ![(cylinderEuclideanEquiv x).1 0,
      (cylinderEuclideanEquiv x).1 1, 0] i := by
  rw [model_horizontal_symm, model_horizontal_basis_left]

set_option maxHeartbeats 1600000 in
-- The finite four-index identity expands the explicit stereographic curvature.
/-- The actual cylinder curvature tensor on every coordinate basis tuple.
Source: the limiting cylinder in Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_curvature_basis {t : ℝ} (ht : t < 1)
    (x : E) (i j k l : Fin 3) :
    jetCurvature (metricTwoJet (evolvingCylinderModelField t) x) (e i) (e j) (e k) (e l) =
      (512 * (1 - t) / modelCylinderDenominator x ^ 4) *
        (H (e i) (e k) * H (e j) (e l) - H (e i) (e l) * H (e j) (e k)) := by
  let J := metricTwoJet (evolvingCylinderModelField t) x
  change (2⁻¹ : ℝ) *
      (fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x (e i) (e l) (e j) (e k) -
        fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x (e i) (e k) (e j) (e l) -
        fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x (e j) (e l) (e i) (e k) +
        fderiv ℝ (fderiv ℝ (evolvingCylinderModelField t)) x (e j) (e k) (e i) (e l)) +
    (-fderiv ℝ (evolvingCylinderModelField t) x (e i) (jetChristoffel J (e j) (e l)) (e k) +
      fderiv ℝ (evolvingCylinderModelField t) x (e j) (jetChristoffel J (e i) (e l)) (e k) +
      evolvingCylinderModelField t x (jetChristoffel J (e i) (jetChristoffel J (e j) (e l))) (e k) -
      evolvingCylinderModelField t x
        (jetChristoffel J (e j) (jetChristoffel J (e i) (e l))) (e k)) = _
  simp only [model_evolvingCylinderField_second, model_evolvingCylinderField_first,
    model_evolvingCylinderField_apply]
  dsimp only [J]
  simp only [model_evolvingCylinder_christoffel_horizontal ht,
    model_evolvingCylinder_christoffel_horizontal_right ht,
    model_evolvingCylinder_christoffel_height ht, zero_mul, add_zero]
  have hxx : H x x = ‖(cylinderEuclideanEquiv x).1‖ ^ 2 := by
    rw [cylinderHorizontalForm_apply, real_inner_self_eq_norm_sq]
  rw [hxx]
  simp_rw [cylinderHorizontalForm_basis]
  simp only [model_horizontal_basis_left,
    model_horizontal_basis_right, modelCylinderDenominator,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hden : (cylinderEuclideanEquiv x).1 0 ^ 2 +
      (cylinderEuclideanEquiv x).1 1 ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [cylinderHorizontalGram, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left] <;>
    field_simp [hden] <;> ring_nf

end PoincareMT.M45
