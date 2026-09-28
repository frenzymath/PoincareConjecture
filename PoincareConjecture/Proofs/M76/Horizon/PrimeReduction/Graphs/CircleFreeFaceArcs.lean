import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents









set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_actual_circle_free_face_arcs
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset E) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hsub : G.space ⊆ convexHull ℝ (t : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : E) ∉ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hboundary : ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Nonempty) :
    G.space = ⋃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∧
    Pairwise (fun C D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
        (D.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      ∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
          Polygon.pathCarrier (fun i => ((e i).val : E)) ∧
        IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
          (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ∧
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
          {((e 0).val : E), ((e (Fin.last (n + 1))).val : E)} ∧
        ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
          (e i.castSucc = v ∧ e i.succ = w) ∨
          (e i.castSucc = w ∧ e i.succ = v) := by
  obtain ⟨hcover, hdis, hcomponents⟩ := G.exists_actual_face_components hG hdim
    t ht hind hsub hfinite hinterior hexterior
  refine ⟨hcover, hdis, fun C => ?_⟩
  rcases hcomponents C with harc | ⟨n, P, _, _, hPC, hPi⟩
  · exact harc
  · obtain ⟨x, hxC, hxf⟩ := hboundary C
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxf
    exact (hxf.2 (hPi (hPC.symm.subset hxC))).elim

end Geometry.SimplicialComplex
