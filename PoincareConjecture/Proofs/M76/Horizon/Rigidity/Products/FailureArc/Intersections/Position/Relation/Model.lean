import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Construction



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

open Classical in
structure SurfaceIntersectionComponents
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Source : Set E) (Target : Set F) (f : E → X) (g : F → X) (rim : Set F) where
  left : SimplicialComplex ℝ E
  right : SimplicialComplex ℝ F
  left_finite : left.faces.Finite
  right_finite : right.faces.Finite
  left_space : left.space = {x | x ∈ Source ∧ f x ∈ g '' Target}
  right_space : right.space = {y | y ∈ Target ∧ g y ∈ f '' Source}
  matching : left.space ≃ₜ right.space
  matching_PL : matching.IsFinitePL
  matching_inv_PL : matching.symm.IsFinitePL
  matching_value : ∀ x : left.space, f x = g (matching x)
  dimension : ∀ b ∈ right.faces, b.card ≤ 2
  degree : ∀ v : right.vertices, (right.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
    if (v : F) ∈ rim then 1 else 2
  pieces : right.vertexAbstractComplex.edgeGraph.ConnectedComponent → Set F
  components_finite : Finite right.vertexAbstractComplex.edgeGraph.ConnectedComponent
  pieces_eq : ∀ C, pieces C = C.toSimpleGraph.segmentCarrier (fun v => (v.val : F))
  cover : right.space = ⋃ C, pieces C
  disjoint : Pairwise (fun C D => Disjoint (pieces C) (pieces D))
  topology : ∀ C, IsCompact (pieces C) ∧ IsConnected (pieces C) ∧
    IsClopen ((Subtype.val : right.space → F) ⁻¹' pieces C)
  models : ∀ C, IsFinitePLBallPair ℝ (pieces C) (pieces C ∩ rim) ∨
    ∃ (n : ℕ) (P : Polygon F (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = pieces C ∧ Disjoint (pieces C) rim
  intrinsic : ConnectedComponents right.space ≃ right.vertexAbstractComplex.edgeGraph.ConnectedComponent
  intrinsic_value : ∀ (x : right.space) C,
    intrinsic (ConnectedComponents.mk x) = C ↔ (x : F) ∈ pieces C
  boundary_count : (ConnectedComponents.mk '' ((Subtype.val : right.space → F) ⁻¹' rim)).ncard =
    {C | (pieces C ∩ rim).Nonempty}.ncard
  interior_count : (ConnectedComponents.mk '' ((Subtype.val : right.space → F) ⁻¹' rim))ᶜ.ncard =
    {C | Disjoint (pieces C) rim}.ncard

theorem nonempty_surface_intersection_components
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
    Nonempty (SurfaceIntersectionComponents K.space L.space f g Q) := by
  classical
  obtain ⟨A, B, H, pieces, hA, hB, hAs, hBs, hH, hHi, hHv, hc, hd,
    hfinite, hpieces, hcover, hdisjoint, htopology, hmodels,
    ⟨c, hcv⟩, hboundaryCount, hinteriorCount⟩ :=
    exists_intrinsic_surface_intersection_components he K L hK hL hf hg hfi hgi Q
      hboundary hinterior
  exact ⟨⟨A, B, hA, hB, hAs, hBs, H, hH, hHi, hHv, hc, hd, pieces,
    hfinite, hpieces, hcover, hdisjoint, htopology, hmodels,
    c, hcv, hboundaryCount, hinteriorCount⟩⟩

end PoincareConjecture.M76
