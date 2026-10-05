import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.OrdinaryBoxes
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countably many ordinary history boxes

The ordinary time windows form a relatively open cover of all nonsurgery
times. A countable subcover suffices, since each box covers its whole regular
slice. Together with one box at each of the finitely many included events,
this gives the countability needed for the history spacetime topology.
Source: Morgan--Tian, Lemma 14.11 and Proposition 14.12, pp. 349-350.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)

/-- A countable selection of the constructed ordinary boxes covers every
point at every included nonsurgery time. -/
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

end PoincareMT.Surgery.RegularHistory
