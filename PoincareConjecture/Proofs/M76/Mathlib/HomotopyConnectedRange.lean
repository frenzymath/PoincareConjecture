import Mathlib.Topology.Homotopy.Path

set_option autoImplicit false

open Set

namespace ContinuousMap.Homotopy

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
