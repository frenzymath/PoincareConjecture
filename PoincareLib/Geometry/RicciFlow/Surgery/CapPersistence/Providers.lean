import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Main

/-!
# Checked M44 analytic predecessor supplier

The supplier applies the actual M04 curvature theory and the literal
Type-`u` ordinary-flow field exported by M13. It introduces no additional
admission and is the closed entry used by M45 and M90.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem m44CapPersistencePredecessorsFromMilestones :
    M44CapPersistencePredecessors.{u} :=
  {
    curvature := ricciFlowCurvatureTheory
    ordinary_flow := (generalizedParabolicRescaling_from_M12 3).ordinary_flow
  }

theorem m44CapPersistenceFromMilestones :
    RepairedCapPersistenceTheory.{u} :=
  repairedCapPersistence m44CapPersistencePredecessorsFromMilestones

end PoincareMT
