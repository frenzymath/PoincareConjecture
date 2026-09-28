import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.Interval.Set.OrdConnected

set_option autoImplicit false

open Set

namespace PoincareConjecture.ChainShape

theorem exists_active_eq_of_ordConnected (S : Set ℤ)
    (hne : S.Nonempty) (hS : Set.OrdConnected S) :
    ∃ shape : ChainShape, shape.active = S := by
  classical
  by_cases hl : BddBelow S
  · have ha := Int.csInf_mem hne hl
    by_cases hu : BddAbove S
    · have hb := Int.csSup_mem hne hu
      refine ⟨.finite (sInf S) (sSup S), ?_⟩
      ext x
      exact ⟨fun hx => hS.out ha hb hx, fun hx => ⟨csInf_le hl hx, le_csSup hu hx⟩⟩
    · refine ⟨.forward (sInf S), ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.mp hu x
        exact hS.out ha hy ⟨hx, hxy.le⟩
      · exact fun hx => csInf_le hl hx
  · by_cases hu : BddAbove S
    · have hb := Int.csSup_mem hne hu
      refine ⟨.backward (sSup S), ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hl x
        exact hS.out hy hb ⟨hyx.le, hx⟩
      · exact fun hx => le_csSup hu hx
    · refine ⟨.biInfinite, ?_⟩
      ext x
      constructor
      · intro _
        obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hl x
        obtain ⟨z, hz, hxz⟩ := not_bddAbove_iff.mp hu x
        exact hS.out hy hz ⟨hyx.le, hxz.le⟩
      · exact fun _ => mem_univ x

end PoincareConjecture.ChainShape
