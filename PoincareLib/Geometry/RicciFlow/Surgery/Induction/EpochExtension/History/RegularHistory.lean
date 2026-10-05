import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory

/-!
# M48's supplied M33 regular-history construction

The actual preterminal slab gives the finite window. Applying the M33
predecessor constructs its generalized regular history; no M49/M50 service
or independently assumed realization is needed here.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem M48Predecessors.regularHistory (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T) :
    Nonempty (M33RegularHistoryData L.regularHistoryWindow) :=
  P.m33.regular_history F L.regularHistoryWindow

end PoincareMT
