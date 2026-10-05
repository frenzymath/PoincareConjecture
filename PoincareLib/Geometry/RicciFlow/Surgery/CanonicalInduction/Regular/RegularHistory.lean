import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory

/-!
# The actual raw history for Proposition 17.1

M28/M30 use this raw generalized flow with its original clock. The caller
constructs the closed history up to an included nonempty slice; it does not
claim that exposed cap points lie in its regular image or produce backward
survival, curvature or volume controls.
Sources: Morgan--Tian Proposition 14.12, p. 350, and Proposition 17.1 /
Lemma 17.2 with the compactness argument, pp. 395-403.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem M47Predecessors.closedRegularHistory (P : M47Predecessors.{u})
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) :
    Nonempty (M33RegularHistoryData (F.closedRegularHistoryWindow T hT hTF ⟨x⟩)) :=
  P.regular_history F _

end PoincareMT
