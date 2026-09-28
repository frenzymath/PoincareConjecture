import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Graphs.Mathlib.ResidualFundamentalCycle
import PoincareConjecture.Proofs.M76.Wall.Mathlib.TreeCotreeResidualEdges

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

theorem exists_paired_cycles_of_residual_edge
    {V : Type*} [Fintype V] [DecidableEq V] (A : AbstractSimplicialComplex V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (P : SimpleGraph V) (hP : P ≤ A.edgeGraph) (hPc : P.Connected)
    (D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph A.toPreAbstractSimplicialComplex P)
    (hDc : D.Connected)
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) :
    let q := complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex P hcofaces
    let e := (q s).val
    ∃ (v : V) (c : A.edgeGraph.Walk v v)
      (t : Triangle A.toPreAbstractSimplicialComplex)
      (d : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).Walk t t),
      c.IsCycle ∧ d.IsCycle ∧
      (∃ p ∈ c.edges, p.toFinset = e.val) ∧ s.val ∈ d.edges ∧
      (∀ p ∈ c.edges, p ∈ P.edgeSet ∨ p.toFinset = e.val) ∧
      (∀ r ∈ d.edges, r ∈ D.edgeSet ∨ r = s.val) ∧
      (∀ f : Edge A.toPreAbstractSimplicialComplex,
        ((∃ p ∈ c.edges, p.toFinset = f.val) ∧
          ∃ r : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet,
            r.val ∈ d.edges ∧ (q r).val = f) ↔ f = e) := by
  classical
  intro q e
  obtain ⟨u, w, huw, he⟩ := Finset.card_eq_two.mp e.property.2
  have hadj : A.edgeGraph.Adj u w := ⟨huw, he ▸ e.property.1⟩
  let p : A.edgeGraph.edgeSet := ⟨s(u, w), hadj⟩
  have hpP : p.val ∉ P.edgeSet := by
    intro hp
    apply (q s).property
    refine ⟨u, w, P.mem_edgeSet.mp hp, ?_⟩
    change e.val = _
    ext x
    rw [he]
    simp
  obtain ⟨v, c, hc, hpc, hcsupport⟩ :=
    SimpleGraph.exists_cycle_through_edge_with_support A.edgeGraph P hP hPc p hpP
  obtain ⟨t, d, hd, hsd, hdsupport⟩ :=
    SimpleGraph.exists_cycle_through_edge_with_support
      (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P) D hD hDc s hs
  have hpval : p.val.toFinset = e.val := by
    exact Sym2.toFinset_mk_eq.trans he.symm
  have hcs (r : Sym2 V) (hr : r ∈ c.edges) :
      r ∈ P.edgeSet ∨ r.toFinset = e.val := by
    rcases hcsupport r hr with h | rfl
    · exact Or.inl h
    · exact Or.inr hpval
  refine ⟨v, c, t, d, hc, hd, ⟨p.val, hpc, hpval⟩, hsd, hcs, hdsupport, ?_⟩
  intro f
  constructor
  · rintro ⟨⟨r, hrc, hrf⟩, a, had, haf⟩
    rcases hcs r hrc with hrP | hre
    · obtain ⟨f', hf', hmark⟩ := A.exists_original_face_of_graph_edge P hP ⟨r, hrP⟩
      have hff : f' = f := Subtype.ext (hf'.trans hrf)
      have hfP : edgeInGraph A.toPreAbstractSimplicialComplex P f := hff ▸ hmark
      exact False.elim ((q a).property (haf.symm ▸ hfP))
    · exact Subtype.ext (hrf.symm.trans hre)
  · rintro rfl
    exact ⟨⟨p.val, hpc, hpval⟩, s, hsd, rfl⟩

end AbstractSimplicialComplex
