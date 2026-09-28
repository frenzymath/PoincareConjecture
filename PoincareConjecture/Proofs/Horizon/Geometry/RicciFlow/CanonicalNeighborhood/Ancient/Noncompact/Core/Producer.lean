import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.VolumeScaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.EscapingScale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture











theorem noncompactKappaUniformCoreEstimates_of_services
    (P : NoncompactKappaServices.{u}) :
    UniformSoulCenteredCoreConclusionOfServices.{u} := by
  exact noncompactKappaUniformCoreEstimates_of_trichotomy_of_services P
    (coreNormalizedCurvatureTrichotomy_of_originalFlow P.classificationServices.curvatureTrichotomy)


theorem noncompactKappaUniformCoreEstimates
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    UniformSoulCenteredCoreConclusion P := by
  exact noncompactKappaUniformCoreEstimates_of_services P.noncompactServices

end PoincareConjecture
