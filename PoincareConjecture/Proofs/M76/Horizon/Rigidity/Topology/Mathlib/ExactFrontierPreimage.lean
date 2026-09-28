import Mathlib.Topology.ContinuousMap.Basic



set_option autoImplicit false
open Set

namespace ContinuousMap

theorem interior_preimage_of_frontier_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) {A : Set Y}
    (h : frontier (q ⁻¹' A) = q ⁻¹' frontier A) :
    interior (q ⁻¹' A) = q ⁻¹' interior A := by
  rw [← self_sdiff_frontier, ← self_sdiff_frontier A, preimage_sdiff, h]

end ContinuousMap
