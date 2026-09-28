import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricEdgeLabels
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.EdgeSubdivisionTree
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalGraphEdges










set_option autoImplicit false

namespace PreAbstractSimplicialComplex

variable {V : Type*} (A : PreAbstractSimplicialComplex V)



theorem faceInclusionGraph_not_adj_of_card_eq (s t : A.faces)
    (hcard : s.val.card = t.val.card) : ¬A.faceInclusionGraph.Adj s t := by
  rintro ⟨hne, hst | hts⟩
  · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hst hcard.ge))
  · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hts hcard.le).symm)



theorem faceInclusionGraph_adj_iff_of_card_lt (s t : A.faces)
    (hcard : s.val.card < t.val.card) : A.faceInclusionGraph.Adj s t ↔ s.val ⊆ t.val := by
  constructor
  · rintro ⟨_, hst | hts⟩
    · exact hst
    · exact (Nat.not_le_of_lt hcard (Finset.card_le_card hts)).elim
  · intro hst
    refine ⟨?_, Or.inl hst⟩
    intro he
    exact (Nat.ne_of_lt hcard) (congrArg (fun q : A.faces => q.val.card) he)

end PreAbstractSimplicialComplex

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {V : Type*} [DecidableEq V] (A : AbstractSimplicialComplex V)
  (T : SimpleGraph V) (hT : T ≤ A.edgeGraph)



noncomputable def primalFaceLabel : V ⊕ T.edgeSet → A.faces
  | Sum.inl v => ⟨{v}, A.singleton_mem v⟩
  | Sum.inr e => ⟨e.val.toFinset, by
      obtain ⟨q, hq, _⟩ := A.exists_original_face_of_graph_edge T hT e
      rw [← hq]
      exact q.property.1⟩



theorem primalFaceLabel_edge_card (e : T.edgeSet) :
    (A.primalFaceLabel T hT (Sum.inr e)).val.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ (T.not_isDiag_of_mem_edgeSet e.property)



theorem primalFaceLabel_injective : Function.Injective (A.primalFaceLabel T hT) := by
  intro x y h
  rcases x with v | e <;> rcases y with w | d
  · exact congrArg Sum.inl (Finset.singleton_injective (congrArg Subtype.val h))
  · have hc := congrArg (fun s : A.faces => s.val.card) h
    change 1 = (A.primalFaceLabel T hT (Sum.inr d)).val.card at hc
    rw [A.primalFaceLabel_edge_card] at hc
    omega
  · have hc := congrArg (fun s : A.faces => s.val.card) h
    change (A.primalFaceLabel T hT (Sum.inr e)).val.card = 1 at hc
    rw [A.primalFaceLabel_edge_card] at hc
    omega
  · exact congrArg Sum.inr
      (Subtype.ext (Sym2.toFinset_injective (congrArg Subtype.val h)))

private theorem primalFaceLabel_mixed_adj (v : V) (e : T.edgeSet) :
    A.toPreAbstractSimplicialComplex.faceInclusionGraph.Adj
      (A.primalFaceLabel T hT (Sum.inl v)) (A.primalFaceLabel T hT (Sum.inr e)) ↔
        v ∈ e.val := by
  rw [A.toPreAbstractSimplicialComplex.faceInclusionGraph_adj_iff_of_card_lt _ _ (by
    change 1 < (A.primalFaceLabel T hT (Sum.inr e)).val.card
    rw [A.primalFaceLabel_edge_card]
    omega)]
  change {v} ⊆ e.val.toFinset ↔ v ∈ e.val
  rw [Finset.singleton_subset_iff, Sym2.mem_toFinset]




noncomputable def primalFaceGraphEmbedding :
    T.incidenceSubdivision ↪g A.toPreAbstractSimplicialComplex.faceInclusionGraph where
  toFun := A.primalFaceLabel T hT
  inj' := A.primalFaceLabel_injective T hT
  map_rel_iff' := by
    intro x y
    rcases x with v | e <;> rcases y with w | d
    · exact iff_false_intro
        (A.toPreAbstractSimplicialComplex.faceInclusionGraph_not_adj_of_card_eq _ _ (by
          change ({v} : Finset V).card = ({w} : Finset V).card
          simp only [Finset.card_singleton]))
    · exact A.primalFaceLabel_mixed_adj T hT v d
    · exact (A.toPreAbstractSimplicialComplex.faceInclusionGraph.adj_comm _ _).trans
        (A.primalFaceLabel_mixed_adj T hT w e)
    · exact iff_false_intro
        (A.toPreAbstractSimplicialComplex.faceInclusionGraph_not_adj_of_card_eq _ _ (by
          change (A.primalFaceLabel T hT (Sum.inr e)).val.card =
            (A.primalFaceLabel T hT (Sum.inr d)).val.card
          rw [A.primalFaceLabel_edge_card, A.primalFaceLabel_edge_card]))



theorem isTree_induce_primalFaceLabels [Finite V] (htree : T.IsTree) :
    (A.toPreAbstractSimplicialComplex.faceInclusionGraph.induce
      (Set.range (A.primalFaceLabel T hT))).IsTree := by
  exact (A.primalFaceGraphEmbedding T hT).isoInduceRange.isTree_iff.mp
    (SimpleGraph.IsTree.incidenceSubdivision T htree)

end AbstractSimplicialComplex
