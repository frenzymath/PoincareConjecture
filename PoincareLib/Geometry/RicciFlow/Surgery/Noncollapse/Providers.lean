import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Main
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Noncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Providers

/-!
# M46 predecessor application

The earlier theorem services are supplied once, before the induction service
is passed to M51. The output still quantifies over the actual selected M45
setup and all its compatible finite prefixes. This adapter adds no admission.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Supply M04/M11/M12/M13/M14/M15 and the actual M33 regular-history service to M46.
Every calibrated M45 setup then admits its prefix-indexed noncollapsing
extension, with one common kappa and a cutoff for each allowed next radius.
Source: Morgan--Tian Proposition 16.1 and Remark 16.2, pp. 367-368, and its
proof through p. 394 using Theorem 8.1, pp. 169-176. This is a checked
application of M46, whose substantive proof remains its single admission. -/
theorem m46NoncollapseInductionFromMilestones :
    RepairedNoncollapseInductionTheory.{u} :=
  repairedNoncollapseInduction
    { m04 := ricciFlowCurvatureTheory
      m11 := generalizedSpacetimeGeometry 3
      m12 := generalizedRicciGaugeGeometry_from_M03_M04_M11 3
      m13 := generalizedParabolicRescaling_from_M12 3
      m14 := generalizedLGeometryTheory_from_predecessors 3
      m15 := (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized
      regular_history := m33BranchContinuationFromMilestones.regular_history }

end PoincareMT
