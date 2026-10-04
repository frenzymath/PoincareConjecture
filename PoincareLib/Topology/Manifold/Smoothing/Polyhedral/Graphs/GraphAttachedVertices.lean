import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Attaching vertices to a connected induced graph

New vertices with actual neighbors in the original carrier
preserve induced-graph preconnectedness. This permits either
sign choice at the former zero vertices of a surface link.
See Alexander 1924, pp. 6--8 and M76 derivation 281.
-/

set_option autoImplicit false

open Set

namespace SimpleGraph

/-- An induced preconnected graph remains preconnected
after adding vertices each adjacent to an original vertex.
The empty original carrier forces the enlarged carrier
empty. See M76 derivation 281. -/
theorem Preconnected.induce_of_attached_vertices
    {V : Type*} {G : SimpleGraph V} {s t : Set V}
    (hG : (G.induce s).Preconnected) (hst : s ⊆ t)
    (hattach : ∀ x ∈ t, x ∉ s → ∃ y ∈ s, G.Adj x y) :
    (G.induce t).Preconnected := by
  have hanchor (x : t) : ∃ y : s,
      (G.induce t).Reachable x ⟨y, hst y.property⟩ := by
    by_cases hx : (x : V) ∈ s
    · exact ⟨⟨x, hx⟩, Reachable.rfl⟩
    · obtain ⟨y, hy, hxy⟩ := hattach x x.property hx
      exact ⟨⟨y, hy⟩, (show (G.induce t).Adj x ⟨y, hst hy⟩ from hxy).reachable⟩
  intro a b
  obtain ⟨u, hau⟩ := hanchor a
  obtain ⟨v, hbv⟩ := hanchor b
  exact hau.trans (((hG u v).map (G.induceHomOfLE hst).toHom).trans hbv.symm)

end SimpleGraph
