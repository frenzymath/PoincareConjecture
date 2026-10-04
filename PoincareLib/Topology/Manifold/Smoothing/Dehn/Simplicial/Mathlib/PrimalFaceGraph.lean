import PoincareLib.Topology.Manifold.Smoothing.Dehn.Barycentric.Mathlib.BarycentricEdgeLabels
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Barycentric.Mathlib.EdgeSubdivisionTree
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.OriginalGraphEdges

/-!
# The literal primal color in the original face graph

Original vertices label singleton faces and actual primal edges label
their entire two-endpoint faces. The induced graph on precisely these
labels is the incidence subdivision of the same original graph.
See Putman, Theorem 5.1, pp. 15--16, and Dehn derivation 021, section 1.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex

variable {V : Type*} (A : PreAbstractSimplicialComplex V)

/-- Distinct comparable faces cannot have the same cardinality.
See the full face-chain description in Dehn derivation 021, section 1. -/
theorem faceInclusionGraph_not_adj_of_card_eq (s t : A.faces)
    (hcard : s.val.card = t.val.card) : ¬A.faceInclusionGraph.Adj s t := by
  rintro ⟨hne, hst | hts⟩
  · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hst hcard.ge))
  · exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hts hcard.le).symm)

/-- For different face sizes the full graph adjacency is exactly the
inclusion from the smaller face to the larger one. See Dehn 021, section 1. -/
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

/-- Literal primal labels: original vertices give singleton faces and
original graph edges give their full endpoint faces. See Dehn 021, section 1. -/
noncomputable def primalFaceLabel : V ⊕ T.edgeSet → A.faces
  | Sum.inl v => ⟨{v}, A.singleton_mem v⟩
  | Sum.inr e => ⟨e.val.toFinset, by
      obtain ⟨q, hq, _⟩ := A.exists_original_face_of_graph_edge T hT e
      rw [← hq]
      exact q.property.1⟩

/-- Each edge label retains both original endpoints.
See Dehn derivation 021, section 1. -/
theorem primalFaceLabel_edge_card (e : T.edgeSet) :
    (A.primalFaceLabel T hT (Sum.inr e)).val.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ (T.not_isDiag_of_mem_edgeSet e.property)

/-- The primal labels never identify distinct original vertices or
distinct whole original edges. See Dehn derivation 021, section 1. -/
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

/-- The full primal face-label graph is precisely the original incidence
subdivision, with adjacency preserved in both directions.
See Dehn derivation 021, section 1. -/
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

/-- The actual full graph on the primal labels is a tree when the
original primal graph is a tree. See Dehn derivation 021, section 1. -/
theorem isTree_induce_primalFaceLabels [Finite V] (htree : T.IsTree) :
    (A.toPreAbstractSimplicialComplex.faceInclusionGraph.induce
      (Set.range (A.primalFaceLabel T hT))).IsTree := by
  exact (A.primalFaceGraphEmbedding T hT).isoInduceRange.isTree_iff.mp
    (SimpleGraph.IsTree.incidenceSubdivision T htree)

end AbstractSimplicialComplex
