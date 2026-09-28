import PoincareConjecture.Proofs.M48.RegularHistory
import PoincareConjecture.Proofs.M12.GeneralizedRicci

set_option autoImplicit false

universe u

namespace PoincareConjecture

structure M48RegularSpacetimeData {F : SurgeryFlowData.{u}} {T : ℝ}
    (L : RepairedPreterminalSlab F T) where
  history : M33RegularHistoryData L.regularHistoryWindow
  geometry : Proofs.M12.FlowBoxRicciGeometry history.generalized

theorem M48Predecessors.regularSpacetime (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T) :
    Nonempty (M48RegularSpacetimeData L) := by
  obtain ⟨H⟩ := P.regularHistory L
  obtain ⟨G⟩ := Proofs.M12.flowBoxRicciGeometry H.generalized P.m11 P.m12
  exact ⟨⟨H, G⟩⟩

end PoincareConjecture
