import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Standard.Curvature.StandardCapTransfer
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Distance.MetricComparison
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Transition.SurgeryTransitionMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrder
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Standard.Cylindrical.CylindricalBoundary
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckChart

/-! Existing metric producers under their published source names. -/

namespace PoincareMT.M36

export PoincareMT.MetricSurgery
  (centeredNeckDomain neck_retained_iff
   neg_negativeCurvaturePart_le_sectional_of_orthonormal
   sectionalCurvature_eq_of_local_isometry metric_edist_le_pathELength
   metric_pathELength_add centeredCylinderLift_basis_gram centeredCylinderComponent
   cylindrical_carrier_eq cylindrical_zero_radial centeredNeckLift_mem
   centeredNeckInverse centeredNeckInverse_contMDiffAt_lift centeredNeckInverse_lift)

end PoincareMT.M36
