import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareLib.Geometry.RicciFlow.Positivity.Scalar.StrongMaximum
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedAtlas
import PoincareLib.Geometry.Spacetime.Realization.Interval.Topology

/-! Source spellings for the pinned deep-horn construction. -/

namespace PoincareMT.DeepHornSource

scoped macro "GeneralizedBoundedDistanceHypotheses" : term =>
  `(PoincareMT.DenseGeneralizedBoundedDistanceHypotheses)

scoped macro "RepairedGeneralizedBoundedDistanceTheory" ".{" u:level "}" : term =>
  `(PoincareMT.DenseGeneralizedBoundedDistanceTheory.{$u})

scoped macro "RepairedGeneralizedBoundedDistanceTheory" : term =>
  `(PoincareMT.DenseGeneralizedBoundedDistanceTheory)

end PoincareMT.DeepHornSource

namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis
  (ricciFlow_supersolution_positive_at_later_time)
end PoincareMT.M04

namespace PoincareMT.M13
export PoincareMT.Homothety (homothety_curvatureTensorNorm_eq)
end PoincareMT.M13

namespace PoincareMT.Proofs.M11
export Poincare.Spacetime.Realization (interval_uniqueDiffOn)
end PoincareMT.Proofs.M11

namespace PoincareMT.Proofs.M12
export PoincareMT.EpochExtension.Spacetime
  (flowBoxAtlas_realize flowSlice_identification)
end PoincareMT.Proofs.M12

namespace PoincareMT.Proofs.M15
export PoincareMT.Generalized.Noncollapse
  (calibratedMetricVolume_eq_euclideanHausdorff)
end PoincareMT.Proofs.M15
