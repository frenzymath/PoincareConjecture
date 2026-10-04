import Mathlib.Topology.Homotopy.Path

/-!
# Connectedness of deformation neighborhoods

A homotopy from the identity to a map with path-connected range makes
its whole domain path connected. This supplies connected open stages in
Hatcher's tower, Theorem 3.1, pp. 45--46; see M76 derivation 315.
-/

set_option autoImplicit false

open Set

namespace ContinuousMap.Homotopy

/-- Paths along the homotopy and inside its endpoint range connect any
two points of the original domain. See Hatcher Theorem 3.1, pp. 45--46
and M76 derivation 315. -/
theorem pathConnectedSpace_of_range
    {X : Type*} [TopologicalSpace X] {r : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy r) (hr : IsPathConnected (range r)) :
    PathConnectedSpace X := by
  obtain ⟨x, hx⟩ := hr.nonempty
  refine ⟨⟨x⟩, fun a b => ?_⟩
  exact (show Joined a (r a) from ⟨H.evalAt a⟩).trans
    ((hr.joinedIn (r a) (mem_range_self a) (r b) (mem_range_self b)).joined.trans
      (show Joined b (r b) from ⟨H.evalAt b⟩).symm)

end ContinuousMap.Homotopy
