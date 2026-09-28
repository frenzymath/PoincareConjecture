import PoincareConjecture.Statements.M47CanonicalInduction
import PoincareConjecture.Proofs.M33.RegularHistory












set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem M47Predecessors.closedRegularHistory (P : M47Predecessors.{u})
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) :
    Nonempty (M33RegularHistoryData (F.closedRegularHistoryWindow T hT hTF ⟨x⟩)) :=
  P.regular_history F _

end PoincareConjecture
