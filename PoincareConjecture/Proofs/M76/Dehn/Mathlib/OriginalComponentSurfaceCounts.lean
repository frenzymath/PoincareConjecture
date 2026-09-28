import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponentConnected
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComponentCochainExactness
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleIncidenceRanks










set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)



theorem edgeComponentComplex_triangle_cofaces
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (K.edgeComponentComplex C).vertices]
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    ∀ e : Edge (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex,
      (triangleCofaces
        (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex e).card =
          2 := by
  intro e
  rw [(K.edgeComponentComplex C).triangleCofaces_card_eq_original e,
    K.edgeComponentComplex_cofaces C e.property.1 3]
  apply hcofaces _ (K.edgeComponentComplex_le C e.property.1)
  simpa only [Finset.card_map] using e.property.2




theorem edgeComponentComplex_triangle_connected
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected) :
    (triangleGraph
      (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex).Connected :=
  by
    apply (K.edgeComponentComplex C).vertex_triangleGraph_connected
    apply (K.edgeComponentComplex C).triangleGraph_connected_of_links
      (K.edgeComponentComplex_pure C hpure) (K.edgeComponentComplex_connected C)
    intro p hp
    rw [K.edgeComponentComplex_vertex_link C hp]
    exact hlinks p (K.edgeComponentComplex_le C hp)




theorem edgeComponentComplex_surface_count [Fintype K.vertices]
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected)
    (hexact : LinearMap.ker
      (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) :
    let L := (K.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex
    Nat.card (K.edgeComponentComplex C).vertices + Nat.card (Triangle L) =
      Nat.card (Edge L) + 2 := by
  classical
  let J := K.edgeComponentComplex C
  let i := K.subcomplexVertexEmbedding J (K.edgeComponentComplex_le C)
  let : Fintype J.vertices := Fintype.ofInjective i i.injective
  exact J.vertexAbstractComplex.triangle_incidence_count_of_two_cofaces
    (K.edgeComponentComplex_connected C) (K.edgeComponentComplex_edge_exactness C hexact)
    (K.edgeComponentComplex_triangle_cofaces C hcofaces)
    (K.edgeComponentComplex_triangle_connected C hpure hlinks)

end Geometry.SimplicialComplex
