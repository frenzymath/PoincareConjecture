import PoincareConjecture.Proofs.M46
import PoincareConjecture.Proofs.M15.Providers
import PoincareConjecture.Proofs.M33.Providers

set_option autoImplicit false

universe u

namespace PoincareConjecture

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

end PoincareConjecture
