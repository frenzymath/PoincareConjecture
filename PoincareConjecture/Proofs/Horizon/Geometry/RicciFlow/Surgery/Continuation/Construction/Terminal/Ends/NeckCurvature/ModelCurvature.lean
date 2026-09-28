import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ModelJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ScalarBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateBounds




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

theorem roundCylinderEuclideanMetric_first_jet_zero :
    fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients 0 = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply roundCylinderEuclideanBasis.ext
  intro i
  change fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients 0
    (roundCylinderEuclideanBasis i) = 0
  apply ContinuousLinearMap.coe_injective
  apply roundCylinderEuclideanBasis.ext
  intro j
  change fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients 0
    (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) = 0
  apply ContinuousLinearMap.coe_injective
  apply roundCylinderEuclideanBasis.ext
  intro k
  change fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients 0
    (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
      (roundCylinderEuclideanBasis k) = 0
  rw [← LeviCivitaData.iteratedFDeriv_one_metric_inner, iteratedFDeriv_one_apply]
  exact roundCylinderEuclideanMetric_first_scalar_jet_zero j k i

theorem roundCylinderEuclideanMetric_second_jet (i j k l : Fin 3) :
    fderiv ℝ (fderiv ℝ roundCylinderEuclideanMetric.euclideanCoefficients) 0
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
      (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l) =
      -2 * inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1 *
        inner ℝ (roundCylinderCoordinateBasis k).1 (roundCylinderCoordinateBasis l).1 := by
  rw [← LeviCivitaData.iteratedFDeriv_two_metric_inner, iteratedFDeriv_two_apply]
  exact roundCylinderEuclideanMetric_second_scalar_jet k l i j

theorem roundCylinderEuclideanMetric_curvature_zero_basis
    (D : LeviCivitaData roundCylinderEuclideanMetric) (i j k l : Fin 3) :
    D.curvatureTensor 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)
      (roundCylinderEuclideanBasis k) (roundCylinderEuclideanBasis l) =
        NeckCurvature.cylinderCurvatureComponent i j k l := by
  rw [D.curvatureTensor_eq_second_deriv_add_firstKind,
    roundCylinderEuclideanMetric_first_jet_zero]
  simp only [roundCylinderEuclideanMetric_second_jet, metricKoszulCovector,
    zero_apply, ContinuousLinearMap.flip_zero,
    zero_add, sub_zero, smul_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [NeckCurvature.cylinderCurvatureComponent, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, PiLp.single_apply,
      Fin.ext_iff]

end PoincareConjecture
