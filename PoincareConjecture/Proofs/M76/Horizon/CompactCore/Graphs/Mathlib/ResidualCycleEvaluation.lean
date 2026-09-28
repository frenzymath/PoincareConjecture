import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Graphs.Mathlib.ResidualPairedCycles
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Graphs.Mathlib.DualWalkCochain
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.CocycleWalkValue










set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {V : Type*} [DecidableEq V] {A : AbstractSimplicialComplex V}



theorem walkValue_eq_count_of_edge_indicator
    (c : A.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle)
    (e : Sym2 V) {u v : V} (w : A.edgeGraph.Walk u v)
    (hvalue : ∀ {x y : V} (_h : A.edgeGraph.Adj x y), s(x, y) ∈ w.edges →
      c.value x y = if s(x, y) = e then 1 else 0) :
    c.walkValue w = (w.edges.count e : ZMod 2) := by
  classical
  induction w with
  | nil => simp [walkValue]
  | @cons u v w h p ih =>
    rw [walkValue, hvalue h (by simp)]
    rw [ih (fun h' hh => hvalue h' (List.mem_cons_of_mem _ hh))]
    by_cases he : s(u, v) = e <;>
      simp [SimpleGraph.Walk.edges_cons, he, add_comm]

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex




theorem exists_detected_cycle_of_residual_edge
    {V : Type*} [Fintype V] [DecidableEq V] (A : AbstractSimplicialComplex V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (P : SimpleGraph V) (hP : P ≤ A.edgeGraph) (hPc : P.Connected)
    (D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph A.toPreAbstractSimplicialComplex P)
    (hDc : D.Connected)
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) :
    ∃ (z : Edge A.toPreAbstractSimplicialComplex → ZMod 2)
      (hz : edgeCoboundary A.toPreAbstractSimplicialComplex z = 0)
      (v : V) (c : A.edgeGraph.Walk v v), c.IsCycle ∧
      (cocycleOfClosed A.toPreAbstractSimplicialComplex z hz).walkValue c = 1 := by
  classical
  let Q := A.toPreAbstractSimplicialComplex
  let q := complementaryTriangleEdgeEquiv Q P hcofaces
  let e := (q s).val
  obtain ⟨v, c, t, d, hc, hd, ⟨p, hpc, hpe⟩, hsd, hcs, _, _⟩ :=
    A.exists_paired_cycles_of_residual_edge hcofaces P hP hPc D hD hDc s hs
  let z := dualWalkCochain Q P hcofaces d
  have hz : edgeCoboundary Q z = 0 := dualWalkCochain_closed Q P hcofaces d
  have hze : z e = 1 := by
    exact dualWalkCochain_eq_one_of_isTrail Q P hcofaces d hd.isTrail s hsd
  have hvalue : ∀ {x y : V} (h : A.edgeGraph.Adj x y), s(x, y) ∈ c.edges →
      (cocycleOfClosed Q z hz).value x y = if s(x, y) = p then 1 else 0 := by
    intro x y h hxy
    change edgeValue Q z x y = _
    have hface := pair_mem_faces Q h.2 (Finset.mem_insert_self x {y})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rw [edgeValue_pair Q z x y hface h.1]
    let f := pairEdge Q x y hface h.1
    by_cases hp : s(x, y) = p
    · have hfe : f = e := by
        apply Subtype.ext
        ext a
        rw [← hpe]
        simp only [f, pairEdge, Finset.mem_insert, Finset.mem_singleton, Sym2.mem_toFinset]
        rw [← hp]
        exact Sym2.mem_iff.symm
      change z f = _
      rw [hfe, hze, if_pos hp]
    · rw [if_neg hp]
      have hfP : edgeInGraph Q P f := by
        rcases hcs s(x, y) hxy with hPxy | heq
        · refine ⟨x, y, P.mem_edgeSet.mp hPxy, ?_⟩
          ext a
          simp [f, pairEdge]
        · exact False.elim (hp (Sym2.toFinset_injective (heq.trans hpe.symm)))
      exact dualWalkCochain_eq_zero_on_primal Q P hcofaces d f hfP
  refine ⟨z, hz, v, c, hc, ?_⟩
  rw [PreAbstractSimplicialComplex.ModTwoEdgeCocycle.walkValue_eq_count_of_edge_indicator
    _ p c hvalue, hc.isTrail.count_edges_eq_one hpc]
  rfl

end AbstractSimplicialComplex
