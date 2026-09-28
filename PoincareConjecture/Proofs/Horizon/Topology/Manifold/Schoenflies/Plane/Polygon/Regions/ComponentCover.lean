import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

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
