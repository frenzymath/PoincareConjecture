import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryTriangleEdges

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

theorem exists_primal_dual_trees_with_residual_edges
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)
    (hconn : A.edgeGraph.Connected)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (htri : (triangleGraph A.toPreAbstractSimplicialComplex).Connected) :
    ∃ P : SimpleGraph ι, P ≤ A.edgeGraph ∧ P.IsTree ∧
      ∃ D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex),
        D ≤ complementaryTriangleGraph A.toPreAbstractSimplicialComplex P ∧ D.IsTree ∧
        ∃ L : Finset (Edge A.toPreAbstractSimplicialComplex),
          (∀ e, e ∈ L ↔
            ∃ s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet,
              (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex
                P hcofaces s).val = e ∧ s.val ∉ D.edgeSet) ∧
          (∀ e ∈ L, ¬edgeInGraph A.toPreAbstractSimplicialComplex P e) ∧
          Nat.card ι + Nat.card (Triangle A.toPreAbstractSimplicialComplex) + L.card =
            Nat.card (Edge A.toPreAbstractSimplicialComplex) + 2 := by
  classical
  obtain ⟨P, hP, hPtree⟩ := hconn.exists_isTree_le
  let G := complementaryTriangleGraph A.toPreAbstractSimplicialComplex P
  have hG : G.Connected := complementaryTriangleGraph_connected
    A.toPreAbstractSimplicialComplex P hPtree.isAcyclic hcofaces htri
  obtain ⟨D, hD, hDtree⟩ := hG.exists_isTree_le
  let q := complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex P hcofaces
  let label : G.edgeSet → Edge A.toPreAbstractSimplicialComplex := fun s => (q s).val
  have hlabel : Function.Injective label := by
    intro s t h
    exact q.injective (Subtype.ext h)
  let U : Finset G.edgeSet := Finset.univ.filter (fun s => s.val ∉ D.edgeSet)
  let L := U.image label
  have hL (e : Edge A.toPreAbstractSimplicialComplex) :
      e ∈ L ↔ ∃ s : G.edgeSet, label s = e ∧ s.val ∉ D.edgeSet := by
    simp only [L, U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨s, he, hs⟩
    · rintro ⟨s, he, hs⟩
      exact ⟨s, hs, he⟩
  have hLcard : L.card = Nat.card {s : G.edgeSet // s.val ∉ D.edgeSet} := by
    change (U.image label).card = _
    rw [Finset.card_image_of_injective U hlabel,
      Nat.card_eq_fintype_card, Fintype.card_subtype]

  have hprimalPartition : Nat.card P.edgeSet + Nat.card G.edgeSet =
      Nat.card (Edge A.toPreAbstractSimplicialComplex) := by
    change Nat.card P.edgeSet +
      Nat.card (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet = _
    rw [A.card_original_graph_edges P hP,
      card_complementary_triangle_edges A.toPreAbstractSimplicialComplex P hcofaces,
      ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (edgeInGraph A.toPreAbstractSimplicialComplex P))
  let selectedEquiv : {s : G.edgeSet // s.val ∈ D.edgeSet} ≃ D.edgeSet :=
    { toFun := fun s => ⟨s.val.val, s.property⟩
      invFun := fun s => ⟨⟨s.val, SimpleGraph.edgeSet_mono hD s.property⟩, s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hdualPartition : Nat.card D.edgeSet +
      Nat.card {s : G.edgeSet // s.val ∉ D.edgeSet} = Nat.card G.edgeSet := by
    rw [← Nat.card_congr selectedEquiv, ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun s : G.edgeSet => s.val ∈ D.edgeSet))
  have hPcard := (SimpleGraph.isTree_iff_connected_and_card.mp hPtree).2
  have hDcard := (SimpleGraph.isTree_iff_connected_and_card.mp hDtree).2
  refine ⟨P, hP, hPtree, D, hD, hDtree, L, hL, ?_, ?_⟩
  · intro e he
    obtain ⟨s, rfl, _⟩ := (hL e).mp he
    exact (q s).property
  · omega

end AbstractSimplicialComplex
