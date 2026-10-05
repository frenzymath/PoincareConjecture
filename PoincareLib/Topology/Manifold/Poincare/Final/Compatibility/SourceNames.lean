import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Carrier.BallRetention
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Cutoff.Geometric
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Product.StableSurvival
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SmallTime.Confinement.SmallTimeEnergy
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Continuation.ContinuationBackward
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Barrier.PathComparison
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.ScalarDifferentialBound
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveCylinderLines
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.SmallBallVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.PhysicalBirthMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.Confinement.OverlapCaps
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.BackwardFiniteEvents
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.BackwardOrdinaryCylinder
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.CanonicalBall
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.CapBirth
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.SeedCurvature
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapMetricScalingGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CapMetricScalingScalar
import PoincareLib.Topology.Homotopy.Sphere.SphereConnectivity

/-! Source-name exports for unchanged Mapher endpoint-provider proofs. -/

namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis
  (abs_ricci_le_curvatureTensorNorm
   compact_subset_min_velocity_nonnegative_Icc
   compact_subset_min_velocity_nonnegative_of_upper_support
   connection_difference_pairing
   contDiffOn_curvatureTensor_timeSlice
   contMDiffOn_extend_baseSet
   contMDiffOn_flow_iteratedCovariantTensorDerivative
   contMDiffOn_flow_tensorNorm_sq
   contMDiffOn_mvfderiv_spatial
   contMDiffOn_shi_connection
   contMDiff_tensorNorm_sq
   continuousOn_flow_ricciNormSq
   continuousOn_flow_timeDependentLaplacian
   covariantTensorDerivativeOnFields
   covariantTensorDerivativeOnFields_eq
   curvatureTensor_swap_first
   curvatureTensor_swap_last
   curvature_self
   exists_compact_carrier_for_flow_balls
   exists_shi_geometric_cutoff
   exists_shi_metric_frame
   frameGramOperator
   frameGramOperator_isInvertible
   frameInverseGram
   frameInverseGram_eq_coordinate_sum
   initial_ball_isOpen
   initial_half_ball_closure_subset_initial_ball
   isSmoothCovariantTensor_covariantTensorDerivative
   isSmoothCovariantTensor_ricciEvaluation
   isSmoothCovariantTensor_riemannEvaluation
   isCompact_modelOrthonormalPairs
   laplacian_sub_of_contMDiffOn
   metricGram
   metricGram_pos_of_linearIndependent
   metric_derivative_pairing
   modelOrthonormalPairs
   nonneg_ricci_of_nonnegativeSectionalAt
   nonneg_scalar_of_nonnegativeSectionalAt
   ricci_symm
   shiPhysicalCutoffSupports
   shiRetainedFlowRadius
   tensorEvaluation_sq_le_tensorNorm
   tensorNorm_sq_eq_inverseGram)
end PoincareMT.M04

namespace PoincareMT.M08
export PoincareMT.LGeometry
  (backwardPathOfSqrt
   backwardPathOfSqrt_action
   continuationAction_intervalIntegrable
   regularizedLAction
   regularizedLAction_eq_backwardLLength
   regularizedLIntegrand)
end PoincareMT.M08

namespace PoincareMT.M09
export PoincareMT.ReducedLength
  (isCompact_closure_metric_ball
   reducedLength_le_path)
end PoincareMT.M09

namespace PoincareMT.M10
export PoincareMT.ReducedVolume
  (abs_scalarCurvature_le
   calibratedMetricVolume_image_eq_lintegral)
end PoincareMT.M10

namespace PoincareMT.M13
export PoincareMT.Homothety
  (curvatureTensorLinear
   edist_le_pathELength
   exists_pathELength_lt
   homothety_ball_image
   homothety_curvatureTensorNorm_eq
   homothety_edist
   homothety_ricci_eq
   homothety_scalarCurvature_eq
   homothety_sectionalCurvature_eq
   homothety_volume_image
   metricHomothetyCalculus
   ricciLinear
   ricciLinear_apply
   scaleLeviCivitaData
   scaleSmoothMetric
   scaleSmoothMetric_inner
   scaleSmoothMetric_tangentNorm)
end PoincareMT.M13

namespace PoincareMT.M13
export PoincareMT.ParabolicRescaling
  (identity_metricHomothety
   ordinaryParabolicRescaling)
end PoincareMT.M13

namespace PoincareMT.Proofs.M02
export Poincare.Topology
  (sphere_simplyConnectedSpace_of_two_lt_finrank)
end PoincareMT.Proofs.M02

namespace PoincareMT.Proofs.M03
export PoincareMT.RicciFlow.Local
  (exists_curvature_trilinearMap
   ricci_eq_sum_basis_of_curvature_pairing)
end PoincareMT.Proofs.M03

namespace PoincareMT.Proofs.M09
export PoincareMT.ReducedLength
  (exists_smoothJoin_uniform_density
   integral_join_error_bound
   isCompact_closure_metric_ball
   reducedLength_le_path
   scalarCurvature_mvfderiv_abs_le
   squareCurveActionDensity
   squareCurveActionDensity_congr
   squareCurveActionDensity_contDiffOn)
end PoincareMT.Proofs.M09

namespace PoincareMT.Proofs.M12
export PoincareMT.EpochExtension.Spacetime
  (cylinderPhysicalInterval
   flowBoxAtlas
   flowBoxRicciGeometry
   flowInterval
   rawCylinderMap
   rawCylinderMap_at_parameter
   rawCylinderMap_embedding
   rawCylinderMap_time
   rawCylinderMetric
   rawCylinderMetric_eq
   rawCylinderTransport)
end PoincareMT.Proofs.M12

namespace PoincareMT.Proofs.M13
export PoincareMT.EpochExtension.SliceGeometry
  (originalSlice_ball
   originalSlice_scalar)
end PoincareMT.Proofs.M13

namespace PoincareMT.Proofs.M15
export PoincareMT.Generalized.Noncollapse
  (calibratedMetricVolume_ball_lt_top_of_precompact
   calibratedMetricVolume_eq_volumeMeasure
   exists_stableSet_of_minimizing)
end PoincareMT.Proofs.M15

namespace PoincareMT.Proofs.M15
export PoincareMT.EpochExtension.Noncollapse
  (rawActualBallCylinder)
end PoincareMT.Proofs.M15
