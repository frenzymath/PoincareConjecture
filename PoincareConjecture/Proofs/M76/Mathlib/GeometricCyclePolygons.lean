import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon










set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [Finite V] [AddCommGroup E] [Module ℝ E]




theorem exists_polygon_of_two_neighbors (G : SimpleGraph V) (p : V → E)
    (hconn : G.Connected) (hdegree : ∀ v, (G.neighborSet v).ncard = 2)
    (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = G.segmentCarrier p := by
  obtain ⟨n, e, he⟩ := G.exists_cyclic_labels_of_two_neighbors hconn hdegree
  let P : Polygon E (n + 3) := ⟨fun i => p (e i)⟩
  have hadj (i : Fin (n + 3)) : G.Adj (e i) (e (i + 1)) :=
    (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨n, P, hinj.comp e.injective, ?_, (G.segmentCarrier_eq_polygonBoundary p e he).symm⟩
  intro i j
  simpa only [Polygon.edgeSet, Polygon.edgeVertices, Finset.coe_pair,
    affineSegment_eq_segment, finRotate_apply] using
    (hinter (hadj i) (hadj j))




theorem exists_component_polygons_of_two_neighbors (G : SimpleGraph V) (p : V → E)
    (hdegree : ∀ v, (G.neighborSet v).ncard = 2) (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    ∃ (n : G.ConnectedComponent → ℕ) (P : ∀ C, Polygon E (n C + 3)),
      (∀ C, Function.Injective (P C) ∧ (P C).HasSimplicialEdges ∧
        (P C).boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => p v.val)) ∧
      G.segmentCarrier p = ⋃ C, (P C).boundary ℝ ∧
      Pairwise (fun C D => Disjoint ((P C).boundary ℝ) ((P D).boundary ℝ)) := by
  have hex (C : G.ConnectedComponent) :=
    C.toSimpleGraph.exists_polygon_of_two_neighbors (fun v => p v.val)
      C.connected_toSimpleGraph
      (fun v => (C.ncard_neighborSet G v).trans (hdegree v.val))
      (hinj.comp Subtype.val_injective) (fun {_ _ _ _} hvw hab => hinter hvw hab)
  choose n P hinjP hinterP hbound using hex
  refine ⟨n, P, fun C => ⟨hinjP C, hinterP C, hbound C⟩, ?_, ?_⟩
  · simp only [hbound, G.segmentCarrier_eq_iUnion_components p]
  · simpa only [hbound] using G.pairwise_disjoint_component_segmentCarrier p hinj hinter

end SimpleGraph
