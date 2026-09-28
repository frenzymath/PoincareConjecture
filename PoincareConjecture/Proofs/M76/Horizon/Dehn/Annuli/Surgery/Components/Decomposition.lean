import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.OrdinaryCircles



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in


structure SourceCircleDecomposition
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → X) (S : Set E) where
  graph : SimplicialComplex ℝ E
  partner : graph.space ≃ₜ graph.space
  finite : graph.faces.Finite
  space : graph.space = doubleLocusOn f S
  partnerPL : partner.IsFinitePL
  partnerInvPL : partner.symm.IsFinitePL
  involutive : Function.Involutive partner
  free : ∀ x : graph.space, (partner x : E) ≠ x
  value : ∀ x : graph.space, f (partner x) = f x
  unique : ∀ (x : graph.space) (y : E), y ∈ S → (x : E) ≠ y →
    f x = f y → y = (partner x : E)
  face_card : ∀ a ∈ graph.faces, a.card ≤ 2
  degree : ∀ v : graph.vertices, (graph.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2
  n : graph.vertexAbstractComplex.edgeGraph.ConnectedComponent → ℕ
  polygon : ∀ A, Polygon E (n A + 3)
  mate : Equiv.Perm graph.vertexAbstractComplex.edgeGraph.ConnectedComponent
  finite_components : Finite graph.vertexAbstractComplex.edgeGraph.ConnectedComponent
  model : ∀ A, Function.Injective (polygon A) ∧ (polygon A).HasSimplicialEdges ∧
    (polygon A).boundary ℝ = A.toSimpleGraph.segmentCarrier (fun v ↦ (v.val : E))
  cover : graph.space = ⋃ A, (polygon A).boundary ℝ
  disjoint : Pairwise (fun A B ↦ Disjoint ((polygon A).boundary ℝ) ((polygon B).boundary ℝ))
  topology : ∀ A, IsCompact ((polygon A).boundary ℝ) ∧
    IsConnected ((polygon A).boundary ℝ) ∧
    IsClopen ((Subtype.val : graph.space → E) ⁻¹' (polygon A).boundary ℝ)
  mate_involutive : Function.Involutive mate
  partner_component : ∀ A (x : graph.space), (x : E) ∈ (polygon A).boundary ℝ ↔
    (partner x : E) ∈ (polygon (mate A)).boundary ℝ
  image_mate : ∀ A, f '' (polygon (mate A)).boundary ℝ = f '' (polygon A).boundary ℝ
  image_disjoint : ∀ A B, A ≠ B → mate A ≠ B →
    Disjoint (f '' (polygon A).boundary ℝ) (f '' (polygon B).boundary ℝ)

theorem nonempty_sourceCircleDecomposition
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) (hR : MapsTo f K.space R)
    (hclosed : IsClosed (doubleLocusOn f K.space))
    (hinterior : MapsTo f (doubleLocusOn f K.space) (interior R))
    (hcross : ∀ x ∈ K.space, ∀ y ∈ K.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f K.space R x y))
    (hunique : ∀ x ∈ K.space, ∀ y ∈ K.space, ∀ z ∈ K.space,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z) :
    Nonempty (SourceCircleDecomposition f K.space) := by
  obtain ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hcard, hdegree,
    n, P, mate, hfin, hmodel, hcover, hdis, htop, hm2, hmem, himage, himagedis⟩ :=
    exists_ordinary_source_circle_components he K hK hf hR hclosed hinterior hcross hunique
  exact ⟨⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hcard, hdegree,
    n, P, mate, hfin, hmodel, hcover, hdis, htop, hm2, hmem, himage, himagedis⟩⟩

end PoincareConjecture.M76.Dehn.Annuli

