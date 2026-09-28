import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryTriangleEdges











set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)




theorem exists_primal_complementary_trees (hconn : A.edgeGraph.Connected)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (htri : (triangleGraph A.toPreAbstractSimplicialComplex).Connected)
    (hcount : Nat.card ι + Nat.card (Triangle A.toPreAbstractSimplicialComplex) =
      Nat.card (Edge A.toPreAbstractSimplicialComplex) + 2) :
    ∃ T : SimpleGraph ι, T ≤ A.edgeGraph ∧ T.IsTree ∧
      (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).IsTree := by
  classical
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  have hdual := complementaryTriangleGraph_connected A.toPreAbstractSimplicialComplex
    T hT.isAcyclic hcofaces htri
  have hTcard := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  have hpartition : Nat.card T.edgeSet +
      Nat.card (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).edgeSet =
        Nat.card (Edge A.toPreAbstractSimplicialComplex) := by
    rw [A.card_original_graph_edges T hle,
      card_complementary_triangle_edges A.toPreAbstractSimplicialComplex T hcofaces,
      ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (edgeInGraph A.toPreAbstractSimplicialComplex T))
  refine ⟨T, hle, hT, SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hdual, ?_⟩⟩
  omega

end AbstractSimplicialComplex
