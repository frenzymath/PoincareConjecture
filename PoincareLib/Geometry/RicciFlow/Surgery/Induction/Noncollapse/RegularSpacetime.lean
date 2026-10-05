import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedRicci

/-!
# The actual regular history for Proposition 16.1

M33 constructs the history and M11/M12 realize its own boxes. Included
closed windows need no preterminal slab or maximal-domain equality.
Source: Morgan--Tian Proposition 14.12, p. 350, and the use of the smooth
part in the completion of Proposition 16.1, pp. 393-394.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M12
export PoincareMT.EpochExtension.Spacetime (FlowBoxRicciGeometry)
end PoincareMT.Proofs.M12
namespace PoincareMT.Proofs.M12
export PoincareMT.EpochExtension.Spacetime (flowBoxRicciGeometry)
end PoincareMT.Proofs.M12

namespace PoincareMT

structure M46RegularSpacetimeData {F : SurgeryFlowData.{u}}
    (W : M33RegularHistoryWindow F) where
  history : M33RegularHistoryData W
  geometry : Proofs.M12.FlowBoxRicciGeometry history.generalized

theorem M46Predecessors.regularSpacetime (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F) :
    Nonempty (M46RegularSpacetimeData W) := by
  obtain ⟨H⟩ := P.regular_history F W
  obtain ⟨G⟩ := Proofs.M12.flowBoxRicciGeometry H.generalized P.m11 P.m12
  exact ⟨⟨H, G⟩⟩

theorem M46Predecessors.closedRegularSpacetime (P : M46Predecessors.{u})
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain)
    (x : (F.slice T).carrier) :
    Nonempty (M46RegularSpacetimeData (F.closedRegularHistoryWindow T hT hTF ⟨x⟩)) :=
  P.regularSpacetime _

/-- A positive-radius closed test cylinder already has positive terminal time. -/
theorem SurgeryFlowCylinder.test_time_pos
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {T r : ℝ} {U : Set C.carrier} (hr : 0 < r)
    (e : SurgeryFlowCylinder F C T 1 (Icc (-r ^ 2) 0) U) : 0 < T := by
  have ht := F.time_domain_nonnegative (e.time_subset
    ⟨-r ^ 2, ⟨le_rfl, neg_nonpos.mpr (sq_nonneg r)⟩, rfl⟩)
  simp only [div_one, mem_Ici] at ht
  nlinarith [sq_pos_of_pos hr]

end PoincareMT
