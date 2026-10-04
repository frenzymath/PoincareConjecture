import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Topology.Manifold.NeckCap.Theory
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Integer intervals and the four chain shapes

A nonempty order-connected integer set has attained endpoints whenever
bounded. It is therefore exactly one of the four active domains in
Morgan--Tian A.12-A.18, pp. 504-507. See the reviewed fair finite-extension
plan, K1, in tasks/M25/case-local/maximal-chain-plan.md.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.ChainShape

/-- Every nonempty integer interval is the active set of a frozen chain
shape. MT A.12-A.18, pp. 504-507; covering-chain plan K1. -/
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

end PoincareMT.ChainShape
