import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusEuler
import PoincareConjecture.Proofs.M76.Wall.OriginalComponentResidualEdges
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.General.OriginalComponentEssentialPolygon
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation










set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

theorem exists_original_torus_residual_edges
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (A.edgeComponentComplex c).vertices]
    (hzero : (A.edgeComponentComplex c).surfaceEulerCount = 0) :
    ∃ (P : SimpleGraph (A.edgeComponentComplex c).vertices),
      P ≤ (A.edgeComponentComplex c).vertexAbstractComplex.edgeGraph ∧ P.IsTree ∧
      ∃ (D : SimpleGraph (Triangle
          (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex)),
        D ≤ complementaryTriangleGraph
          (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P ∧
        D.IsTree ∧
        ∃ (L : Finset (Edge
            (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex)),
          (∀ e, e ∈ L ↔ ∃ s :
            (complementaryTriangleGraph
              (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet,
              (complementaryTriangleEdgeEquiv
                (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P
                (A.edgeComponentComplex_triangle_cofaces c hcofaces) s).val = e ∧
              s.val ∉ D.edgeSet) ∧
          (∀ e ∈ L, ¬edgeInGraph
            (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P e) ∧
          L.card = 2 := by
  let J := A.edgeComponentComplex c
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLnot, hcount⟩ :=
    A.exists_edgeComponent_trees_with_residual_edges hA c hpure hcofaces hlinks
  have hvertices := J.surfaceEulerCount_eq_vertex_counts
  rw [hzero] at hvertices
  change Nat.card J.vertices + Nat.card (Triangle
    J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + L.card =
    Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 at hcount
  have hcountInt := congrArg (fun n : ℕ => (n : ℤ)) hcount
  have hLcard : L.card = 2 := by
    simp only [Nat.cast_add, Nat.cast_ofNat] at hcountInt
    have hvertices' : (Nat.card J.vertices : ℤ) -
        Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) = 0 := by
      simpa using hvertices.symm
    omega
  exact ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLnot, hLcard⟩

theorem exists_original_torus_essential_polygon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hzero : (A.edgeComponentComplex c).surfaceEulerCount = 0) :
    let J := A.edgeComponentComplex c
    let : Fintype J.vertices :=
      (J.finite_vertices_of_finite_faces (hA.subset (A.edgeComponentComplex_le c))).fintype
    ∃ (z : Edge
        J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2)
      (hz : edgeCoboundary
        J.vertexAbstractComplex.toPreAbstractSimplicialComplex z = 0)
      (v : J.vertices)
      (w : J.vertexAbstractComplex.edgeGraph.Walk v v),
      w.IsCycle ∧ (cocycleOfClosed
        J.vertexAbstractComplex.toPreAbstractSimplicialComplex z hz).walkValue w = 1 ∧
      ∃ (n : ℕ) (P : Polygon E (n + 3))
        (hbase : P 0 = (v : E))
        (hsub : P.boundary ℝ ⊆ J.space),
        n + 3 = w.length ∧
        (∀ i : Fin (n + 3), P i = (w.getVert i.val : E)) ∧
        Function.Injective P ∧ P.HasSimplicialEdges ∧
        (∀ i, P.edgeVertices i ∈ J.faces) ∧
        ¬((P.boundaryLoop.map (continuous_inclusion hsub)).cast
          (Subtype.ext (a1 := (⟨v, J.vertices_subset_space v.property⟩ : J.space)) hbase.symm)
          (Subtype.ext (a1 := (⟨v, J.vertices_subset_space v.property⟩ : J.space)) hbase.symm)).Homotopic
            (Path.refl _) := by
  classical
  let J := A.edgeComponentComplex c
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hA.subset (A.edgeComponentComplex_le c))).fintype
  dsimp only
  have hvertices := J.surfaceEulerCount_eq_vertex_counts
  rw [hzero] at hvertices
  have hpositive : Nat.card J.vertices + Nat.card (Triangle
      J.vertexAbstractComplex.toPreAbstractSimplicialComplex) <
      Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    have hvertices' : (Nat.card J.vertices : ℤ) -
        Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
        Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) = 0 := by
      simpa using hvertices.symm
    omega
  exact Geometry.SimplicialComplex.exists_edgeComponent_essential_polygon
    A hA c hpure hcofaces hlinks hpositive

end PoincareConjecture.M76
