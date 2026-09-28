import PoincareConjecture.Statements.M46NoncollapseInduction
import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M12.GeneralizedRicci

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

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

theorem SurgeryFlowCylinder.test_time_pos
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {T r : ℝ} {U : Set C.carrier} (hr : 0 < r)
    (e : SurgeryFlowCylinder F C T 1 (Icc (-r ^ 2) 0) U) : 0 < T := by
  have ht := F.time_domain_nonnegative (e.time_subset
    ⟨-r ^ 2, ⟨le_rfl, neg_nonpos.mpr (sq_nonneg r)⟩, rfl⟩)
  simp only [div_one, mem_Ici] at ht
  nlinarith [sq_pos_of_pos hr]

end PoincareConjecture
