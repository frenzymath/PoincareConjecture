import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Convergence
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.VolumeScaling
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.EscapingScale
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Estimates
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Assembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy

/-!
# Universal soul-centered core producer

The proof follows Morgan--Tian, Proposition 9.85(1), pp. 237--239.  The
escaping-point contradiction, terminal strong-neck stability, and original
flow splitting interfaces are coordinated producers and are deliberately not
replaced by an M26/M27 conclusion here.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Universal soul-centered core estimates from the seven shared services.

The declaration is the exact source-facing target. Soul-based limit neck
exclusion, noncompactness of limits, curvature-scale separation, and the exact
upper-curvature and volume estimates are proved in the imported core modules.
The universal neck radius is proved by the escaping-point construction and
connectedness propagation. The positive sectional lower bound and the full
assembly use the proved original-flow trichotomy, transported to the
normalized limit carriers.
-/
theorem noncompactKappaUniformCoreEstimates_of_services
    (P : NoncompactKappaServices.{u}) :
    UniformSoulCenteredCoreConclusionOfServices.{u} := by
  exact noncompactKappaUniformCoreEstimates_of_trichotomy_of_services P
    (coreNormalizedCurvatureTrichotomy_of_originalFlow P.classificationServices.curvatureTrichotomy)

/-- The original M26 producer retains its source-facing signature. -/
theorem noncompactKappaUniformCoreEstimates
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    UniformSoulCenteredCoreConclusion P := by
  exact noncompactKappaUniformCoreEstimates_of_services P.noncompactServices

end PoincareMT
