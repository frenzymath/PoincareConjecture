import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A cycle through an actual residual edge

A simple path in the retained connected subgraph closes across the chosen
missing edge. The cycle contains that edge and otherwise uses only the
original subgraph. See Wall derivation 019, lines 133--143.
-/

set_option autoImplicit false

namespace SimpleGraph

/-- Close an actual simple path across an edge outside the connected
subgraph, retaining the exact original edge support. See Wall019. -/
theorem exists_cycle_through_edge_with_support
    {V : Type*} (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.Connected)
    (e : G.edgeSet) (he : e.val ∉ T.edgeSet) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ e.val ∈ c.edges ∧
      ∀ f ∈ c.edges, f ∈ T.edgeSet ∨ f = e.val := by
  classical
  rcases e with ⟨e, heG⟩
  induction e using Sym2.ind with
  | h u v =>
    have huv : G.Adj u v := G.mem_edgeSet.mp heG
    obtain ⟨p, hp⟩ := (hT v u).exists_isPath
    let q := p.mapLe hTG
    have hmissing : s(u, v) ∉ q.edges := by
      rw [Walk.edges_mapLe_eq_edges]
      exact fun h => he (p.edges_subset_edgeSet h)
    refine ⟨u, Walk.cons huv q,
      (Walk.cons_isCycle_iff q huv).mpr ⟨hp.mapLe hTG, hmissing⟩, ?_, ?_⟩
    · simp
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact Or.inr rfl
      · apply Or.inl
        exact p.edges_subset_edgeSet ((Walk.edges_mapLe_eq_edges hTG p) ▸ hf)

end SimpleGraph
