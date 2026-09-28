import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open Set

namespace SimpleGraph

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
