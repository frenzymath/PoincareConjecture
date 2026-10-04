import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedRicci

/-!
# The actual M48 regular-history spacetime

Apply the supplied M33 service on the preterminal window, then the supplied
M11/M12 services to its actual boxes. Retain both selections, the exact
original-slice identifications and the intrinsic equation. This checked bridge
adds no geometric or analytic premise and no admission.
Sources: Morgan--Tian Definitions 3.34-3.38, pp. 59-61, and Lemma 14.11 /
Proposition 14.12, pp. 349-350.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M48RegularSpacetimeData {F : SurgeryFlowData.{u}} {T : ℝ}
    (L : RepairedPreterminalSlab F T) where
  history : M33RegularHistoryData L.regularHistoryWindow
  geometry : EpochExtension.Spacetime.FlowBoxRicciGeometry history.generalized

/-- A preterminal slab supplies the actual generalized regular history and
its same-carrier intrinsic Ricci geometry from M33, M11 and Spacetime. The resulting
M14 transport is `geometry.toLGeometry`; metric/curvature consequences and
the analytic or noncollapse configurations are separate obligations. -/
theorem M48Predecessors.regularSpacetime (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T) :
    Nonempty (M48RegularSpacetimeData L) := by
  obtain ⟨H⟩ := P.regularHistory L
  obtain ⟨G⟩ := EpochExtension.Spacetime.flowBoxRicciGeometry H.generalized P.m11 P.m12
  exact ⟨⟨H, G⟩⟩

end PoincareMT
