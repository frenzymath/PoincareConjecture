import Mathlib.Topology.Connected.Basic

/-!
# Components of an open disjoint cover

A topological auxiliary for the polygonal separation theorem of Cairns
(1951), Theorem 2.1, pp. 860-861. A preconnected member of an open disjoint
cover is the entire component of each of its points in the covered set.
See `smale/derivations/2026-09-21-polygon-regions.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

/-- An open preconnected part of an open disjoint cover is an actual component;
auxiliary to Cairns, Theorem 2.1, pp. 860-861. -/
theorem connectedComponentIn_eq_of_open_disjoint_cover {X : Type*}
    [TopologicalSpace X] {U V W : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hdis : Disjoint U V) (hcover : U ∪ V = W) (hconn : IsPreconnected U)
    {x : X} (hx : x ∈ U) : connectedComponentIn W x = U := by
  have hUW : U ⊆ W := fun _ hz => hcover ▸ Or.inl hz
  have hK : connectedComponentIn W x ⊆ U ∪ V := by
    rw [hcover]
    exact connectedComponentIn_subset W x
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hU hV hdis hK ⟨x, mem_connectedComponentIn (hUW hx), hx⟩
  · exact hconn.subset_connectedComponentIn hx hUW

end Poincare.Manifold.Schoenflies.Plane
