import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.OrdinaryGraph
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.PolygonComponents

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in
theorem exists_ordinary_source_circle_components
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
    ∃ (G : SimplicialComplex ℝ E) (partner : G.space ≃ₜ G.space),
      G.faces.Finite ∧ G.space = doubleLocusOn f K.space ∧
      partner.IsFinitePL ∧ partner.symm.IsFinitePL ∧ Function.Involutive partner ∧
      (∀ x : G.space, (partner x : E) ≠ x) ∧
      (∀ x : G.space, f (partner x) = f x) ∧
      (∀ (x : G.space) (y : E), y ∈ K.space → (x : E) ≠ y →
        f x = f y → y = (partner x : E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      ∃ (n : G.vertexAbstractComplex.edgeGraph.ConnectedComponent → ℕ)
        (P : ∀ A, Polygon E (n A + 3))
        (mate : Equiv.Perm G.vertexAbstractComplex.edgeGraph.ConnectedComponent),
        Finite G.vertexAbstractComplex.edgeGraph.ConnectedComponent ∧
        (∀ A, Function.Injective (P A) ∧ (P A).HasSimplicialEdges ∧
          (P A).boundary ℝ =
            A.toSimpleGraph.segmentCarrier (fun v ↦ (v.val : E))) ∧
        G.space = ⋃ A, (P A).boundary ℝ ∧
        Pairwise (fun A B ↦ Disjoint ((P A).boundary ℝ) ((P B).boundary ℝ)) ∧
        (∀ A, IsCompact ((P A).boundary ℝ) ∧ IsConnected ((P A).boundary ℝ) ∧
          IsClopen ((Subtype.val : G.space → E) ⁻¹' (P A).boundary ℝ)) ∧
        Function.Involutive mate ∧
        (∀ A (x : G.space), (x : E) ∈ (P A).boundary ℝ ↔
          (partner x : E) ∈ (P (mate A)).boundary ℝ) ∧
        (∀ A, f '' (P (mate A)).boundary ℝ = f '' (P A).boundary ℝ) ∧
        ∀ A B, A ≠ B → mate A ≠ B →
          Disjoint (f '' (P A).boundary ℝ) (f '' (P B).boundary ℝ) := by
  obtain ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hcard, hdegree⟩ :=
    exists_finite_interior_double_graph he K hK hf hR hclosed hinterior hcross hunique
  refine ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hcard, hdegree, ?_⟩
  exact exists_paired_polygon_components G hG (fun _ hx ↦ (hGs.subset hx).1)
    hcard hdegree partner hp hp2 hvalue hmate

theorem double_image_interior_of_proper_rim
    {E X : Type*} [TopologicalSpace X] {f : E → X} {S B : Set E} {R : Set X}
    (hR : MapsTo f S R)
    (hproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ B)
    (hdis : Disjoint (doubleLocusOn f S) B) :
    MapsTo f (doubleLocusOn f S) (interior R) := by
  intro x hx
  have hnot : f x ∉ frontier R := fun h ↦
    disjoint_left.mp hdis hx ((hproper x hx.1).mp h)
  have hcl : f x ∈ closure R := subset_closure (hR hx.1)
  by_contra hni
  exact hnot ⟨hcl, hni⟩

end PoincareConjecture.M76.Dehn.Annuli
