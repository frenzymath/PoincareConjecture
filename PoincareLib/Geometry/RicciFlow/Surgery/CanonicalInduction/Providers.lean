import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Main
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Noncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Blowup
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Providers

/-!
# Actual earlier services for M47

The single M47 construction receives curvature calculus, ordinary M08-M10
services, generalized M11-M15 services, geometric compactness and the actual
M33 history service before a calibrated setup or flow is chosen.
Producing each compactness hypothesis remains M47's mathematical obligation.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem m47PredecessorsFromMilestones : M47Predecessors.{u} := {
  m04 := ricciFlowCurvatureTheory
  ordinary := m15OrdinaryProvidersFromMilestones 3
  m11 := generalizedSpacetimeGeometry 3
  m12 := generalizedRicciGaugeGeometry_from_M03_M04_M11 3
  m13 := generalizedParabolicRescaling_from_M12 3
  m14 := generalizedLGeometryTheory_from_predecessors 3
  m15 := (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized
  geometric_limits := m30ControlledGeneralizedBlowupLimitsFromMilestones.geometric_long
  regular_history := m33BranchContinuationFromMilestones.regular_history
}

/-- Apply the one M47 construction to the actual earlier milestone outputs. -/
theorem m47CanonicalInductionFromMilestones : RepairedCanonicalInductionTheory.{u} :=
  repairedCanonicalInduction m47PredecessorsFromMilestones

/-- Theorem 4.23's strictly positive connected branch, supplied by the same
M47 construction; this checked projection introduces no further admission. -/
theorem m47PositiveComponentBlowupFromMilestones :
    M47PositiveComponentBlowupStatement.{u} :=
  m47CanonicalInductionFromMilestones.positive_component_blowup

end PoincareMT
