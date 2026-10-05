import PoincareLib.Analysis.Parabolic.Maximum.Compact
import PoincareLib.Geometry.RicciFlow.Blowup.Sequence
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderSpatial
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.Spacetime.Realization.Interval.Topology

/-! Original declaration names for the mechanically imported blowup construction. -/

namespace PoincareMT.M13
export PoincareMT.Homothety
  (pathELength_eq_lintegral_tangentNorm exists_pathELength_lt
    scaleSmoothMetric_tangentNorm homothety_curvatureTensorNorm_eq)
end PoincareMT.M13

namespace PoincareMT.Proofs.M12
export PoincareMT.EpochExtension.Spacetime
  (rawForward_differential_injective)
end PoincareMT.Proofs.M12

namespace PoincareMT.M04
export PoincareMT.RicciFlowAnalysis
  (compact_min_velocity_nonnegative)
end PoincareMT.M04

namespace PoincareMT.Proofs.M11
export Poincare.Spacetime.Realization (interval_uniqueDiffOn)
end PoincareMT.Proofs.M11

namespace PoincareMT.LeviCivitaData
alias horizon_curvatureDerivativeNorm_zero := curvatureDerivativeNorm_zero
end PoincareMT.LeviCivitaData
