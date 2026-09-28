import PoincareConjecture.Proofs.M76.Horizon.CompactCore.General.OriginalComponentDetectedCycle
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.GeometricWalkDetection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricCyclePolygon
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonCycleLoopComparison

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

theorem exists_edgeComponent_essential_polygon
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
    Nat.card J.vertices + Nat.card (Triangle A) < Nat.card (Edge A) + 2 →
      ∃ (z : Edge A → ZMod 2) (hz : edgeCoboundary A z = 0)
        (v : J.vertices) (c : J.vertexAbstractComplex.edgeGraph.Walk v v),
        c.IsCycle ∧ (cocycleOfClosed A z hz).walkValue c = 1 ∧
        ∃ (n : ℕ) (P : Polygon E (n + 3))
          (hbase : P 0 = (v : E)) (hsub : P.boundary ℝ ⊆ J.space),
          n + 3 = c.length ∧
          (∀ i : Fin (n + 3), P i = (c.getVert i.val : E)) ∧
          Function.Injective P ∧ P.HasSimplicialEdges ∧
          (∀ i, P.edgeVertices i ∈ J.faces) ∧
          ¬((P.boundaryLoop.map (continuous_inclusion hsub)).cast
            (Subtype.ext (a1 := (⟨v, J.vertices_subset_space v.property⟩ : J.space)) hbase.symm)
            (Subtype.ext (a1 := (⟨v, J.vertices_subset_space v.property⟩ : J.space)) hbase.symm)).Homotopic
              (Path.refl _) := by
  classical
  let J := K.edgeComponentComplex C
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hK.subset (K.edgeComponentComplex_le C))).fintype
  dsimp only
  intro hpositive
  obtain ⟨z, hz, v, c, hc, hvalue⟩ :=
    K.exists_edgeComponent_detected_cycle hK C hpure hcofaces hlinks hpositive
  obtain ⟨n, P, hlength, hvertices, hbase, hinj, hedges, hfaces, hsub⟩ :=
    J.exists_polygon_of_geometric_cycle c hc
  have hessential := J.geometricWalk_not_homotopic_refl_of_value_ne_zero
    (cocycleOfClosed J.vertexAbstractComplex.toPreAbstractSimplicialComplex z hz)
    c (by rw [hvalue]; exact one_ne_zero)
  have hcompare := J.polygon_boundaryLoop_homotopic_geometricWalk c P hlength
    hvertices hbase hsub
  refine ⟨z, hz, v, c, hc, hvalue, n, P, hbase, hsub, hlength, hvertices,
    hinj, hedges, hfaces, ?_⟩
  intro hnull
  exact hessential (hcompare.symm.trans hnull)

end Geometry.SimplicialComplex
