import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderCoordinates
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.ModelGram
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M03.MetricInverse












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev CE := EuclideanSpace ℝ (Fin 3)

private abbrev CMetric := MetricCoefficient 3
local instance : NormedAddCommGroup CMetric := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CMetric := ContinuousLinearMap.toNormedSpace
private abbrev CFirst := CE →L[ℝ] CMetric
local instance : NormedAddCommGroup CFirst := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CFirst := ContinuousLinearMap.toNormedSpace
private abbrev CSecond := CE →L[ℝ] CFirst
local instance : NormedAddCommGroup CSecond := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ CSecond := ContinuousLinearMap.toNormedSpace


def cylinderSphereProjection : CE →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderScalarCoordinateEquiv.toContinuousLinearMap


def cylinderAxisProjection : CE →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderScalarCoordinateEquiv.toContinuousLinearMap



def cylinderModelMetricCoefficient (x : CE) : MetricCoefficient 3 :=
  (2 * sphereChartConformalFactor (cylinderSphereProjection x)) •
      (innerSL ℝ).bilinearComp cylinderSphereProjection cylinderSphereProjection +
    (innerSL ℝ).bilinearComp cylinderAxisProjection cylinderAxisProjection


theorem cylinderModelMetricCoefficient_apply (x v w : CE) :
    cylinderModelMetricCoefficient x v w =
      2 * sphereChartConformalFactor (cylinderScalarCoordinateEquiv x).1 *
        inner ℝ (cylinderScalarCoordinateEquiv v).1 (cylinderScalarCoordinateEquiv w).1 +
      (cylinderScalarCoordinateEquiv v).2 * (cylinderScalarCoordinateEquiv w).2 := by
  simp [cylinderModelMetricCoefficient, cylinderSphereProjection, cylinderAxisProjection,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply, mul_comm]



theorem contDiff_cylinderModelMetricCoefficient :
    ContDiff ℝ ∞ cylinderModelMetricCoefficient := by
  exact (contDiff_const.mul
    (contDiff_sphereChartConformalFactor.comp cylinderSphereProjection.contDiff)).smul
      contDiff_const |>.add contDiff_const



theorem cylinderModelMetricCoefficient_basis
    (q : UnitTwoSphere) (s : ℝ) (x : CE) (a b : Fin 3) :
    cylinderModelMetricCoefficient x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (cylinderScalarCoordinates s x) a b := by
  rw [cylinderModelMetricCoefficient_apply,
    cylinderScalarCoordinateEquiv_basis, cylinderScalarCoordinateEquiv_basis,
    roundCylinderGram_chosen_chart]
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateBasis, cylinderScalarCoordinates, Matrix.diagonal,
      EuclideanSpace.inner_single_left, mul_comm]



theorem cylinderModelMetricCoefficient_zero_isInvertible :
    (cylinderModelMetricCoefficient 0).IsInvertible := by
  apply PoincareConjecture.Proofs.M03.isInvertible_bilinear_of_pos
  intro v hv
  rw [cylinderModelMetricCoefficient_apply]
  simp only [map_zero, Prod.fst_zero, sphereChartConformalFactor, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [real_inner_self_eq_norm_sq]
  have hne : cylinderScalarCoordinateEquiv v ≠ 0 := by
    intro hzero
    apply hv
    apply cylinderScalarCoordinateEquiv.injective
    simpa only [map_zero] using hzero
  have hpair : (cylinderScalarCoordinateEquiv v).1 ≠ 0 ∨
      (cylinderScalarCoordinateEquiv v).2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  rcases hpair with hs | ha
  · have hp := sq_pos_of_pos (norm_pos_iff.mpr hs)
    nlinarith [sq_nonneg (cylinderScalarCoordinateEquiv v).2]
  · have hp := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖]


def cylinderModelTwoJet : MetricTwoJet 3 :=
  metricTwoJet cylinderModelMetricCoefficient 0



theorem exists_cylinder_model_scalar_modulus {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ J : MetricTwoJet 3,
      dist J cylinderModelTwoJet < eta →
        |jetScalarCurvature J - jetScalarCurvature cylinderModelTwoJet| < delta :=
  exists_jetScalarCurvature_modulus cylinderModelMetricCoefficient_zero_isInvertible hdelta

end PoincareConjecture.M28.tube
