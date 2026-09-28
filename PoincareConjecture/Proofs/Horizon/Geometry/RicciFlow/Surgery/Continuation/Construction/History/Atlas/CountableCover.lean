import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.OrdinaryBoxes
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)

theorem exists_countable_ordinary_boxes :
    ∃ A : Set (OrdinaryTimeWindow W), A.Countable ∧
      ∀ t ∈ W.interval, t ∉ F.surgery_times → ∀ x : (slice W t).carrier,
        ∃ a ∈ A, ∃ ht : t ∈ a.box.interval,
          ∃ y : a.box.carrier.carrier, a.box.forward t ht y = x := by
  let U (a : OrdinaryTimeWindow W) : Set W.interval :=
    Subtype.val ⁻¹' Ioo a.left a.right
  have hU : ∀ a, IsOpen (U a) := fun _ => isOpen_Ioo.preimage continuous_subtype_val
  have hcover : {t : W.interval | t.val ∉ F.surgery_times} ⊆ ⋃ a, U a := by
    intro t ht
    obtain ⟨a, ha⟩ := exists_ordinaryTimeWindow W t.property ht
    exact mem_iUnion.mpr ⟨a, ha.2⟩
  obtain ⟨A, hA, hAcovers⟩ :=
    (HereditarilyLindelofSpace.isLindelof
      {t : W.interval | t.val ∉ F.surgery_times}).elim_countable_subcover U hU hcover
  refine ⟨A, hA, ?_⟩
  intro t ht hregular x
  obtain ⟨a, ha, hta⟩ := mem_iUnion₂.mp (hAcovers (show (⟨t, ht⟩ : W.interval) ∈
    {s : W.interval | s.val ∉ F.surgery_times} from hregular))
  have htbox : t ∈ a.box.interval := ⟨ht, hta⟩
  obtain ⟨y, hy⟩ := a.box_forward_surjective t htbox x
  exact ⟨a, ha, htbox, y, hy⟩

end PoincareConjecture.Surgery.RegularHistory
