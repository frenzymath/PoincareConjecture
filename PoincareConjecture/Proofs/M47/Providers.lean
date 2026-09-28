import PoincareConjecture.Proofs.M47
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M15.Providers
import PoincareConjecture.Proofs.M30.Providers
import PoincareConjecture.Proofs.M33.Providers

set_option autoImplicit false

universe u

namespace PoincareConjecture

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

theorem m47CanonicalInductionFromMilestones : RepairedCanonicalInductionTheory.{u} :=
  repairedCanonicalInduction m47PredecessorsFromMilestones

theorem m47PositiveComponentBlowupFromMilestones :
    M47PositiveComponentBlowupStatement.{u} :=
  m47CanonicalInductionFromMilestones.positive_component_blowup

end PoincareConjecture
