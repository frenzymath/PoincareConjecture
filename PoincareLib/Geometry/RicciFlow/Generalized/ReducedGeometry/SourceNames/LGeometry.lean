import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.IndexPairAlgebra
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.IndexPositivity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.WeightedJacobiCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.Index.WeightedJacobiIdentities
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.IntervalSolutionUnique
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Jacobi.OverlappingIntervals
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartCoercivity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartEulerRegularity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartRegularity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartStationarity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.WeakVelocity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.ActionBounds
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.PathCongruence
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Path.SquareEnergy
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.EndpointEulerCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.EndpointMomentum
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Regularity.SmoothEndpointExtension
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Coordinates.ChartConnectionVariation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Coordinates.ClosedChartCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationBoundary
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationCoefficients
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.Second.SecondVariationCoordinates
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.SquareVariationConstruction
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.VariationCoordinates
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Variation.VariationIntegral

/-! Source-name facade for the unchanged Mapher proof bodies. -/

namespace PoincareMT.M08

export PoincareMT.LGeometry
  (IntervalSolutionLocality
   affine_chart_density_hasDerivAt
   backwardLLength_congr
   bilinear_curve_hasDerivWithinAt
   chartActionMetric
   chartActionMetric_apply
   chartActionMetric_closed_connection_diagonal
   chartActionMetric_closed_contDiffOn
   chartActionMetric_symm_at
   chartActionMetric_timeWithin
   chartActionMetric_time_pair_interior
   chartActionPotential
   chartActionPotential_apply
   chartActionPotential_closed_contDiffOn
   chartActionPotential_closed_spatial_apply
   chartActionPotential_hessian
   chartChristoffelCovector_apply
   chartCurvatureAlong_apply
   chartForceVector
   chartForceVector_contDiff
   chartForceVector_continuousOn
   chartForceVector_inner
   chartFrame
   chartMetricDualInverse
   chartMetricDualInverse_contDiffOn
   chartMetricDualInverse_left
   chartMetricDualInverse_pair
   chartMetricOperator
   chartMetricOperator_isUnit_of_target
   chartMomentumVector
   chartMomentumVector_inner
   chartRicciForm_at
   chart_momentum_force_intervalIntegrable
   closedChartChristoffel
   closedChartChristoffel_connection
   closedChartChristoffel_pair
   closedChartChristoffel_symm
   closedChartConnection
   closedChartConnection_apply
   closedChartConnection_contDiffOn
   closedChartConnection_spatial_compatibility
   closedChartConnection_time_pair_interior
   closedChartEulerPhase
   closedChartEulerPhase_contDiffOn
   closedChartJacobiPotential
   closedChartJacobiPotential_contDiffOn
   closedChartJacobiPotential_identification
   closedChartJacobiPotential_symm
   closed_time_spatial_commute
   compact_positive_forms_coercive
   contDiffOn_inverse_operator
   continuous_primitive_regular
   coordinateCovariantS
   coordinateCovariantU
   coordinateCurvature
   coordinateCurvature_pair
   coordinatePartialS
   coordinatePartialS_contDiffOn
   coordinatePartialU
   coordinatePartialU_contDiffOn
   coordinateSlice_fst_hasDerivAt
   coordinateSlice_snd_hasDerivAt
   coordinate_mixed_hasDerivAt
   covariantLinearPhaseOperator
   covariantLinearPhaseOperator_contDiffOn
   covariantLinearPhaseOperator_eq_of_pair
   endpoint_momentum_derivative_of_continuous_force
   endpoint_velocity_of_momentum
   exists_enlarged_closed_interval
   exists_interval_solution_of_overlapping_cover
   exists_linear_interval_solution
   exists_overlapping_Icc_partition
   exists_smooth_extension_Icc
   exists_squareTube_radius
   hasDerivAt_deriv_variationIntegral
   hasDerivAt_variationIntegral
   hasDerivAt_variationParameter
   hasDerivWithinAt_timeWithin
   hasFDerivAt_spatial
   hasFDerivAt_spatialWithin
   intervalIntegrable_of_square_transform
   interval_solution_unique_of_cover
   inverse_operator_apply
   linear_interval_solution_contDiffOn
   linear_interval_solution_unique
   mem_closure_interior_Icc_prod
   metricInChart_pos
   metricInChart_symm
   mixedTerm_eq_zero_of_quadratic_nonneg
   positive_form_operator_isUnit
   scalarCurvature_abs_le_tensorNorm
   secondDerivative_nonneg_of_localMin
   spatialFDeriv
   spatialFDeriv_contDiffOn
   spatialWithinFDeriv
   spatialWithinFDeriv_contDiffOn
   spatialWithinFDeriv_eq_spatialFDeriv
   surfaceAccelerationBoundaryPair
   surfaceActionDensity
   surfaceActionDensity_second_boundary
   timeWithinFDeriv
   timeWithinFDeriv_contDiffOn
   variationParameterDeriv
   variationParameterDeriv_contDiffOn
   weak_momentum_of_scalar_stationarity
   weak_momentum_primitive
   weightedChartPotential
   weightedChartPotential_apply)

end PoincareMT.M08
