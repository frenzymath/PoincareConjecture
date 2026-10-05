import PoincareLib.Geometry.RicciFlow.Local.ExistenceUniquenessContinuation
import PoincareLib.Geometry.RicciFlow.Pinching.Imported.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction

open PoincareMT.PinchingImport
/-!
# Applied compact restart and pinching services for M33

These checked applications supply M03 on every constructed compact carrier
and M05 from the actual nonnegative restart time. The concrete singular limit,
calibrated horn geometry, local metric surgery and primitive history bridge
remain inputs of M33's continuation field.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Supply the compact local-flow and absolute-time pinching services by their
actual M03 and M05 theorems. M05 retains its existing M04 dependency. -/
theorem m33BranchContinuationPredecessors : M33Predecessors.{u} := by
  refine {
    local_flow := ricciFlowLocalTheory
    pinching := ?_
  }
  intro M _ _ _ _ _ _ a b ha hab F hinit
  exact hamiltonIveyPinching_from_M04 ha hab F hinit

/-- M33's conditional Lemma 15.11 construction with its compact restart and
pinching services supplied. The singular-limit, calibrated-horn, local-surgery
and primitive history-bridge hypotheses remain explicit in the conclusion. -/
theorem m33BranchContinuationFromMilestones :
    RepairedBranchContinuationTheory.{u} :=
  repairedBranchContinuation m33BranchContinuationPredecessors

end PoincareMT
