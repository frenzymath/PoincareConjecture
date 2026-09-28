import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalFaceLabels
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryFaceColors
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence










set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]




theorem exists_complementary_barycentric_trees
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (T : SimpleGraph K.vertices) (hT : T ≤ K.vertexAbstractComplex.edgeGraph)
    (hprimal : T.IsTree)
    (hdual : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex T).IsTree) :
    ∃ S : Finset K.barycentricSubdivision.vertices,
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)).IsTree ∧
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)ᶜ).IsTree := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces (Set.toFinite _)).fintype
  let : Fintype K.barycentricSubdivision.vertices :=
    (K.barycentricSubdivision.finite_vertices_of_finite_faces
      K.barycentricSubdivision_finite).fintype
  let A := K.vertexAbstractComplex
  have hcounts (e : Edge A.toPreAbstractSimplicialComplex) :
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  have hsize (s : Finset K.vertices) (hs : s ∈ A.faces) : s.card ≤ 3 := by
    have h := hbound (s.map (Function.Embedding.subtype _)) hs
    simpa only [Finset.card_map] using h
  let phi := K.vertexFaceCentroidGraphIso
  let p : T.incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
    (A.primalFaceGraphEmbedding T hT).trans phi.toEmbedding
  let d : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
    (dualFaceGraphEmbedding A.toPreAbstractSimplicialComplex T hcounts).trans phi.toEmbedding
  have hcolors : Set.range d = (Set.range p)ᶜ := by
    change Set.range (phi.toEquiv ∘ dualFaceLabel A.toPreAbstractSimplicialComplex T hcounts) =
      (Set.range (phi.toEquiv ∘ A.primalFaceLabel T hT))ᶜ
    rw [Set.range_comp, Set.range_comp, A.range_dualFaceLabel_eq_compl T hT hcounts hsize]
    exact phi.toEquiv.image_compl _
  let S := (Set.toFinite (Set.range p)).toFinset
  have hS : (S : Set K.barycentricSubdivision.vertices) = Set.range p :=
    (Set.toFinite (Set.range p)).coe_toFinset
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact (SimpleGraph.Embedding.isoInduceRange p).isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision T hprimal)
  · rw [hS, ← hcolors]
    exact (SimpleGraph.Embedding.isoInduceRange d).isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision _ hdual)

end Geometry.SimplicialComplex
