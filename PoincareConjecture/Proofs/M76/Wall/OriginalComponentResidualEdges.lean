import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalComponentSurfaceCounts
import PoincareConjecture.Proofs.M76.Wall.Mathlib.TreeCotreeResidualEdges











set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex




theorem exists_edgeComponent_trees_with_residual_edges
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space) :
    let J := K.edgeComponentComplex C
    let : Fintype J.vertices :=
      (J.finite_vertices_of_finite_faces (hK.subset (K.edgeComponentComplex_le C))).fintype
    let A := J.vertexAbstractComplex.toPreAbstractSimplicialComplex
    ∃ P : SimpleGraph J.vertices, P ≤ J.vertexAbstractComplex.edgeGraph ∧ P.IsTree ∧
      ∃ D : SimpleGraph (Triangle A),
        D ≤ complementaryTriangleGraph A P ∧ D.IsTree ∧
        ∃ L : Finset (Edge A),
          (∀ e, e ∈ L ↔ ∃ s : (complementaryTriangleGraph A P).edgeSet,
            (complementaryTriangleEdgeEquiv A P
              (K.edgeComponentComplex_triangle_cofaces C hcofaces) s).val = e ∧
              s.val ∉ D.edgeSet) ∧
          (∀ e ∈ L, ¬edgeInGraph A P e) ∧
          Nat.card J.vertices + Nat.card (Triangle A) + L.card = Nat.card (Edge A) + 2 := by
  classical
  let J := K.edgeComponentComplex C
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hK.subset (K.edgeComponentComplex_le C))).fintype
  have hlinkgraphs : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected := by
    intro p hp
    exact ((K.faceLink {p}).connected_edgeGraph_of_isConnected
      (SimplicialComplex.finite_faceLink_faces hK _) (hlinks p hp)).preconnected
  exact J.vertexAbstractComplex.exists_primal_dual_trees_with_residual_edges
    (K.edgeComponentComplex_connected C)
    (K.edgeComponentComplex_triangle_cofaces C hcofaces)
    (K.edgeComponentComplex_triangle_connected C hpure hlinkgraphs)

end Geometry.SimplicialComplex
