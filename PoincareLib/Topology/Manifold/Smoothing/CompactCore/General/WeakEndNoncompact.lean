import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import Mathlib.Topology.Connected.Clopen

/-!
# Nonempty new frontier from the literal weak end condition

The larger compact complement in the frozen end predicate is nonempty.
Applying that condition to the whole space rules out compactness.
Thus a nonempty compact core in a connected domain has nonempty
relative frontier. See Wall derivation003, section5.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable {Y : Type*} [TopologicalSpace Y]

/-- The nonempty larger complement in the actual end condition rules
out a compact whole space. See Wall003, section5. -/
theorem HasOneSimplyConnectedEnd.not_isCompact_univ
    (hend : HasOneSimplyConnectedEnd Y) : ¬ IsCompact (univ : Set Y) := by
  intro hY
  obtain ⟨D, _, hYD, hconn, _⟩ := hend univ hY
  obtain ⟨x, hx⟩ := hconn.nonempty
  exact hx (interior_subset (hYD (mem_univ x)))

/-- A nonempty compact core has nonempty frontier in a connected
space with the frozen weak end. See Wall003, section5. -/
theorem HasOneSimplyConnectedEnd.frontier_nonempty_of_isCompact
    [PreconnectedSpace Y] (hend : HasOneSimplyConnectedEnd Y)
    {K : Set Y} (hK : IsCompact K) (hne : K.Nonempty) :
    (frontier K).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨hne, ?_⟩
  intro hKU
  rw [hKU] at hK
  exact hend.not_isCompact_univ hK

end PoincareMT.M76
