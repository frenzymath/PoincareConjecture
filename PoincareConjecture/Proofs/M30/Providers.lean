import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.M25
import PoincareConjecture.Proofs.M28
import PoincareConjecture.Proofs.M29
import PoincareConjecture.Proofs.M30








set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m30ControlledBlowupPredecessorsFromMilestones :
    M30ControlledBlowupPredecessors.{u} := {
  m04 := ricciFlowCurvatureTheory
  m06 := differentialHarnackAncientTheory_from_M04
  m07 := fun H => pointedRicciFlowCompactness_from_M04 H
  m29 := m29GeneralizedBoundedDistance
    (m28BoundedDistance ⟨ricciFlowCurvatureTheory, m25NeckCapTopology⟩)
}

theorem m30ControlledGeneralizedBlowupLimitsFromMilestones :
    RepairedControlledBlowupLimitTheory.{u} :=
  m30ControlledGeneralizedBlowupLimits m30ControlledBlowupPredecessorsFromMilestones

end PoincareConjecture
