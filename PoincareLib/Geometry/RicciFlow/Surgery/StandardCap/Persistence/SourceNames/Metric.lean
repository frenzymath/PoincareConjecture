import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Collapse.RetainedDifferential
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCoordinateJets
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCovariantJets
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderTensorNorm
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrderBounds
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderTwoJet
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Distance.MetricComparison
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckChart
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckMetricBound
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.RadialEquality
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.StandardBalls

/-! Compatibility names for the unchanged Mapher cap-persistence proof. -/

namespace PoincareMT.M36

export PoincareMT.MetricSurgery
  (centeredCylinderBilinear
   centeredCylinderBilinear_basis
   centeredCylinderBilinear_contDiffAt
   centeredCylinderBilinear_gram
   centeredCylinderError
   centeredCylinderError_contDiffAt
   centeredCylinderLift
   centeredCylinderLift_contMDiff
   centeredCylinderLift_mfderiv
   centeredCylinderLift_zero
   centeredCylinderMetric
   centeredCylinderMetric_contDiffAt
   centeredCylinderMetric_sub_model
   centeredNeckDomain_isOpen
   centeredNeckLift
   centeredNeckLift_contMDiffAt
   centeredNeckLift_mfderiv
   centeredNeckLift_mfderiv_isInvertible
   centeredNeckLift_zero
   comparisonChristoffel
   comparisonChristoffel_contDiff
   comparisonTensorComponent
   comparisonTensorComponent_contDiff
   comparisonTensorComponent_covariant
   comparison_bilinear_isSmooth
   comparison_iteratedCovariantTensorDerivative_eventuallyEq
   comparison_tensor_evaluation_bound
   cylinderChristoffelLinear
   cylinderEuclideanEquiv
   cylinderEuclideanEquiv_basis
   cylinderHeightCovector
   cylinderHeightCovector_basis
   cylinderHorizontalCovector
   cylinderHorizontalForm
   cylinderHorizontalForm_add_vertical
   cylinderHorizontalForm_apply
   cylinderHorizontalForm_basis
   cylinderHorizontalGram
   cylinderHorizontalProjection
   cylinderInverseWeight
   cylinderInverseWeight_bounds
   cylinderModelField
   cylinderModelField_contDiff
   cylinderModelField_fderiv_zero
   cylinderModelField_second_fderiv_zero
   cylinderModelField_zero
   cylinderModelField_zero_lower
   cylinderModelJet
   cylinderSphereFactor
   cylinderSphereFactor_contDiff
   cylinderSphereFactor_hasFDerivAt
   diagonal_tensor_product
   edist_comp_le_pathELength_of_pullback_bound
   euclideanThree_bilinear_ext
   euclideanThree_bilinear_norm_le
   exists_centeredCylinderError_jet_bound
   exists_centeredNeckMetric_realization
   exists_compact_local_jet_bound
   exists_comparisonChristoffel_jet_bound
   exists_comparison_covariant_jet_bound
   exists_comparison_smooth_germ
   metricPathSpeed
   metricTwoJet_sub_of_contDiffAt
   metric_edist_continuous
   metric_edist_self
   metric_edist_triangle
   metric_inner_nonneg
   metric_pathELength_mono
   mfderiv_injective_of_local_leftInverse
   neck_central_iff
   neck_coordinate_contMDiffAt
   neck_coordinate_inverse
   neck_coordinate_mem
   neck_inverse_contMDiffAt
   neck_inverse_coordinate
   neck_region_isOpen
   neck_region_subset
   norm_iteratedFDeriv_comp_uniform_at
   norm_iteratedFDeriv_finite_sum
   norm_iteratedFDeriv_smul_uniform_at
   norm_iteratedFDeriv_succ_le_basis
   normalizedNeckConnection
   normalizedNeckForm
   normalizedNeckForm_apply
   normalizedNeckForm_lower
   normalizedNeckMetric
   normalizedNeckMetric_pullbackCoefficients
   pathELength_eq_integral_speed
   radialArclength
   radialArclength_contDiff
   radialArclength_euclideanRadius
   radialArclength_pos
   radialArclength_strictMono
   radialArclength_zero
   radialEuclideanRadius
   radialEuclideanRadius_arclength
   radialEuclideanRadius_contDiff
   radialEuclideanRadius_hasDerivAt
   radialEuclideanRadius_pos_iff
   radialEuclideanRadius_zero
   radialSpeed
   radialSpeed_pos
   radial_path_hasDerivAt
   roundCylinderChristoffel_chart
   roundCylinderClose_error_operator_bounds
   roundCylinderClose_twoJet_error
   roundCylinderTensorNormSquared_center
   sphere_chart_center_zero
   sphere_chart_differential_inner_at
   sphere_chart_inverse_contMDiff
   sphere_chart_inverse_mfderiv
   sphere_chart_target_univ
   standard_ball_eq_euclidean
   standard_closed_ball_compact
   standard_closure_ball
   standard_edist_zero
   standard_frontier_ball
   unit_velocity_of_radial_derivative_one
   zero_mem_centeredNeckDomain)

end PoincareMT.M36
