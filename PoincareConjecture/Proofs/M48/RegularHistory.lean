import PoincareConjecture.Statements.M48EpochExtension
import PoincareConjecture.Proofs.M33.RegularHistory

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem M48Predecessors.regularHistory (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T) :
    Nonempty (M33RegularHistoryData L.regularHistoryWindow) :=
  P.m33.regular_history F L.regularHistoryWindow

end PoincareConjecture
