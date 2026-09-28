import PoincareConjecture.Proofs.M03
import PoincareConjecture.Proofs.M05
import PoincareConjecture.Proofs.M33










set_option autoImplicit false

universe u

namespace PoincareConjecture



theorem m33BranchContinuationPredecessors : M33Predecessors.{u} := by
  refine {
    local_flow := ricciFlowLocalTheory
    pinching := ?_
  }
  intro M _ _ _ _ _ _ a b ha hab F hinit
  exact hamiltonIveyPinching_from_M04 ha hab F hinit




theorem m33BranchContinuationFromMilestones :
    RepairedBranchContinuationTheory.{u} :=
  repairedBranchContinuation m33BranchContinuationPredecessors

end PoincareConjecture
