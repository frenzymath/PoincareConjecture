import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.SourceCarriers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Components
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Germs.Incidence

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

open Classical in
theorem exists_intrinsic_surface_intersection_components
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f K.space) (hg : PolyhedralPLInCharts e g L.space)
    (hfi : InjOn f K.space) (hgi : InjOn g L.space) (Q : Set F)
    (hboundary : ∀ y ∈ L.space ∩ Q, g y ∈ f '' K.space →
      Nonempty (OriginalSurfacePairChart e (f '' K.space) (g '' L.space) (g y) true))
    (hinterior : ∀ y ∈ L.space \ Q, g y ∈ f '' K.space →
      Nonempty (OriginalSurfacePairChart e (f '' K.space) (g '' L.space) (g y) false)) :
    ∃ (A : SimplicialComplex ℝ E) (B : SimplicialComplex ℝ F) (H : A.space ≃ₜ B.space)
      (pieces : B.vertexAbstractComplex.edgeGraph.ConnectedComponent → Set F),
      A.faces.Finite ∧ B.faces.Finite ∧
      A.space = {x | x ∈ K.space ∧ f x ∈ g '' L.space} ∧
      B.space = {y | y ∈ L.space ∧ g y ∈ f '' K.space} ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ (∀ x : A.space, f x = g (H x)) ∧
      (∀ b ∈ B.faces, b.card ≤ 2) ∧
      (∀ v : B.vertices, (B.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : F) ∈ Q then 1 else 2) ∧
      Finite B.vertexAbstractComplex.edgeGraph.ConnectedComponent ∧
      (∀ C, pieces C = C.toSimpleGraph.segmentCarrier (fun v => (v.val : F))) ∧
      B.space = ⋃ C, pieces C ∧
      Pairwise (fun C D => Disjoint (pieces C) (pieces D)) ∧
      (∀ C, IsCompact (pieces C) ∧ IsConnected (pieces C) ∧
        IsClopen ((Subtype.val : B.space → F) ⁻¹' pieces C)) ∧
      (∀ C, IsFinitePLBallPair ℝ (pieces C) (pieces C ∩ Q) ∨
        ∃ (n : ℕ) (P : Polygon F (n + 3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = pieces C ∧ Disjoint (pieces C) Q) ∧
      (∃ c : ConnectedComponents B.space ≃ B.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        ∀ (x : B.space) C, c (ConnectedComponents.mk x) = C ↔ (x : F) ∈ pieces C) ∧
      (ConnectedComponents.mk '' ((Subtype.val : B.space → F) ⁻¹' Q)).ncard =
        {C | (pieces C ∩ Q).Nonempty}.ncard ∧
      (ConnectedComponents.mk '' ((Subtype.val : B.space → F) ⁻¹' Q))ᶜ.ncard =
        {C | Disjoint (pieces C) Q}.ncard := by
  obtain ⟨A, B, H, hA, hB, hAs, hBs, hH, hHinv, hHval, _, _⟩ :=
    hf.exists_paired_intersection_source_carriers he K L hK hL hg hfi hgi
  obtain ⟨hcard, hdegree, hrim⟩ := source_intersection_graph_incidence L B hL hB hg hgi
    (f '' K.space) Q hBs
    (fun y hy => hboundary y ⟨(hBs.subset hy.1).1, hy.2⟩ (hBs.subset hy.1).2)
    (fun y hy => hinterior y ⟨(hBs.subset hy.1).1, hy.2⟩ (hBs.subset hy.1).2)
  obtain ⟨pieces, hfinite, hpieces, hcover, hdisjoint, htopology, hmodels,
      hcomponents, hboundaryCount, hinteriorCount⟩ :=
    Dehn.exists_intrinsic_ordinary_graph_components B Q hB hcard hdegree hrim
  exact ⟨A, B, H, pieces, hA, hB, hAs, hBs, hH, hHinv, hHval, hcard, hdegree,
    hfinite, hpieces, hcover, hdisjoint, htopology, hmodels, hcomponents,
    hboundaryCount, hinteriorCount⟩

end PoincareConjecture.M76
