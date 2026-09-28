import PoincareConjecture.Proofs.M51.EventMaximality
import PoincareConjecture.Proofs.M51.ZeroCapComponents
import PoincareConjecture.Proofs.M51.EventIntervals










set_option autoImplicit false

universe u

namespace PoincareConjecture.SurgeryFlowData



theorem zeroCapDiscard (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3) : RepairedZeroCapDiscard F := by
  intro T hT _ hzero
  exact (F.event T hT).discardedComponent_of_zero_caps hzero
    (F.event_retainedPre_ne_univ H13 hT)

end PoincareConjecture.SurgeryFlowData
