import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.PrimalFaceGraph
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.ComplementaryTriangleEdges

/-!
# The literal complementary color in the original face graph

The complementary edge bijection retains its entire pair of original
triangle cofaces. Triangle labels and non-primal edge labels therefore
induce precisely the incidence subdivision of the complementary graph.
See Putman, Theorem 5.1, pp. 15--16, and Dehn derivation 021, section 1.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)
  (T : SimpleGraph V)
  (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)

/-- The previously constructed complementary edge bijection retains
each of the two whole original triangle cofaces. See Dehn 021, section 1. -/
theorem complementaryTriangleEdgeEquiv_subset
    (s : (complementaryTriangleGraph A T).edgeSet) (q : Triangle A) (hq : q ∈ s.val) :
    (complementaryTriangleEdgeEquiv A T hcofaces s).val.val ⊆ q.val := by
  classical
  change (Classical.choose (exists_unique_complementary_shared_edge A T s).exists).val ⊆ q.val
  exact (Classical.choose_spec (exists_unique_complementary_shared_edge A T s).exists).2 q hq

open Classical in
/-- All original cofaces of the complementary edge label are precisely
the original unordered graph endpoints. See Dehn 021, section 1. -/
theorem complementaryTriangleEdgeEquiv_cofaces
    (s : (complementaryTriangleGraph A T).edgeSet) :
    triangleCofaces A (complementaryTriangleEdgeEquiv A T hcofaces s).val =
      s.val.toFinset :=
  complementary_edge_cofaces A T hcofaces s _
    (complementaryTriangleEdgeEquiv_subset A T hcofaces s)

/-- Literal complementary labels: original triangles give their whole
faces and complementary graph edges give the exact original non-primal
two-vertex faces. See Dehn derivation 021, section 1. -/
noncomputable def dualFaceLabel :
    Triangle A ⊕ (complementaryTriangleGraph A T).edgeSet → A.faces
  | Sum.inl q => ⟨q.val, q.property.1⟩
  | Sum.inr s => ⟨(complementaryTriangleEdgeEquiv A T hcofaces s).val.val,
      (complementaryTriangleEdgeEquiv A T hcofaces s).val.property.1⟩

/-- Original triangle labels retain all three actual vertices.
See Dehn derivation 021, section 1. -/
theorem dualFaceLabel_triangle_card (q : Triangle A) :
    (dualFaceLabel A T hcofaces (Sum.inl q)).val.card = 3 := q.property.2

/-- Complementary edge labels retain both original edge endpoints.
See Dehn derivation 021, section 1. -/
theorem dualFaceLabel_edge_card (s : (complementaryTriangleGraph A T).edgeSet) :
    (dualFaceLabel A T hcofaces (Sum.inr s)).val.card = 2 :=
  (complementaryTriangleEdgeEquiv A T hcofaces s).val.property.2

/-- The complementary labels preserve all original triangles and
non-primal edges without identifications. See Dehn 021, section 1. -/
theorem dualFaceLabel_injective : Function.Injective (dualFaceLabel A T hcofaces) := by
  intro x y h
  rcases x with q | s <;> rcases y with r | t
  · exact congrArg Sum.inl (Subtype.ext (congrArg (fun f : A.faces => f.val) h))
  · have hc := congrArg (fun f : A.faces => f.val.card) h
    rw [dualFaceLabel_triangle_card, dualFaceLabel_edge_card] at hc
    omega
  · have hc := congrArg (fun f : A.faces => f.val.card) h
    rw [dualFaceLabel_edge_card, dualFaceLabel_triangle_card] at hc
    omega
  · apply congrArg Sum.inr
    apply (complementaryTriangleEdgeEquiv A T hcofaces).injective
    exact Subtype.ext (Subtype.ext (congrArg (fun f : A.faces => f.val) h))

private theorem dualFaceLabel_mixed_adj
    (q : Triangle A) (s : (complementaryTriangleGraph A T).edgeSet) :
    A.faceInclusionGraph.Adj (dualFaceLabel A T hcofaces (Sum.inr s))
      (dualFaceLabel A T hcofaces (Sum.inl q)) ↔ q ∈ s.val := by
  classical
  rw [A.faceInclusionGraph_adj_iff_of_card_lt _ _ (by
    rw [dualFaceLabel_edge_card, dualFaceLabel_triangle_card]
    omega)]
  change (complementaryTriangleEdgeEquiv A T hcofaces s).val.val ⊆ q.val ↔ q ∈ s.val
  have h := complementaryTriangleEdgeEquiv_cofaces A T hcofaces s
  calc
    _ ↔ q ∈ triangleCofaces A (complementaryTriangleEdgeEquiv A T hcofaces s).val := by
      simp only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and]
    _ ↔ q ∈ s.val := by rw [h, Sym2.mem_toFinset]

/-- The full graph on complementary labels is exactly the incidence
subdivision of the actual complementary triangle graph.
See Dehn derivation 021, section 1. -/
noncomputable def dualFaceGraphEmbedding :
    (complementaryTriangleGraph A T).incidenceSubdivision ↪g A.faceInclusionGraph where
  toFun := dualFaceLabel A T hcofaces
  inj' := dualFaceLabel_injective A T hcofaces
  map_rel_iff' := by
    intro x y
    rcases x with q | s <;> rcases y with r | t
    · exact iff_false_intro (A.faceInclusionGraph_not_adj_of_card_eq _ _ (by
        change (dualFaceLabel A T hcofaces (Sum.inl q)).val.card =
          (dualFaceLabel A T hcofaces (Sum.inl r)).val.card
        rw [dualFaceLabel_triangle_card, dualFaceLabel_triangle_card]))
    · exact (A.faceInclusionGraph.adj_comm _ _).trans
        (dualFaceLabel_mixed_adj A T hcofaces q t)
    · exact dualFaceLabel_mixed_adj A T hcofaces r s
    · exact iff_false_intro (A.faceInclusionGraph_not_adj_of_card_eq _ _ (by
        change (dualFaceLabel A T hcofaces (Sum.inr s)).val.card =
          (dualFaceLabel A T hcofaces (Sum.inr t)).val.card
        rw [dualFaceLabel_edge_card, dualFaceLabel_edge_card]))

/-- The full graph induced on the complementary face labels is a tree
when the actual complementary graph is a tree. See Dehn 021, section 1. -/
theorem isTree_induce_dualFaceLabels (htree : (complementaryTriangleGraph A T).IsTree) :
    (A.faceInclusionGraph.induce (Set.range (dualFaceLabel A T hcofaces))).IsTree :=
  (dualFaceGraphEmbedding A T hcofaces).isoInduceRange.isTree_iff.mp
    (SimpleGraph.IsTree.incidenceSubdivision _ htree)

end PreAbstractSimplicialComplex.ModTwoCochains
