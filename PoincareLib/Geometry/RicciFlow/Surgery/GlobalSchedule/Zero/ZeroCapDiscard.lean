import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.EventMaximality
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Zero.ZeroCapComponents
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Event.EventIntervals

/-!
# The zero-cap component alternative on the actual flow

Morgan--Tian Lemma 17.12, printed pp. 410-411: a surgery with no inserted
caps removes whole components. Raw event maximality gives properness of
the retained pre-region; its empty boundary then gives a discarded component
of positive pre-event volume. This is not a uniform terminal volume loss.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.SurgeryFlowData

/-- The actual event data supply M49's zero-cap component predicate, using
the existing M13 metric-homothety service for the pre-flow identification. -/
theorem zeroCapDiscard (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) : RepairedZeroCapDiscard F := by
  intro T hT _ hzero
  exact (F.event T hT).discardedComponent_of_zero_caps hzero
    (F.event_retainedPre_ne_univ H13 hT)

end PoincareMT.SurgeryFlowData
