import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {Y : Type*} [TopologicalSpace Y]

theorem HasOneSimplyConnectedEnd.not_isCompact_univ
    (hend : HasOneSimplyConnectedEnd Y) : ¬ IsCompact (univ : Set Y) := by
  intro hY
  obtain ⟨D, _, hYD, hconn, _⟩ := hend univ hY
  obtain ⟨x, hx⟩ := hconn.nonempty
  exact hx (interior_subset (hYD (mem_univ x)))

theorem HasOneSimplyConnectedEnd.frontier_nonempty_of_isCompact
    [PreconnectedSpace Y] (hend : HasOneSimplyConnectedEnd Y)
    {K : Set Y} (hK : IsCompact K) (hne : K.Nonempty) :
    (frontier K).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨hne, ?_⟩
  intro hKU
  rw [hKU] at hK
  exact hend.not_isCompact_univ hK

end PoincareConjecture.M76
