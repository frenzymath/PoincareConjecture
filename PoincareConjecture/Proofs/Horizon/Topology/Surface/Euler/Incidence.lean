import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Cells
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Incidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.Euler

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {I : Type v}

omit [T2Space M] in
theorem coordinate_faceBoundaryIndex_injective (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = coordinates i ∘
      affineChartSegment (basis i (k.succAbove 0)) (basis i (k.succAbove 1))) (i : I) :
    Function.Injective (faceBoundaryIndex face i) := by
  intro k l h
  apply coordinate_edge_images_injective (coordinates i) (basis i) (hsource i)
  simpa only [hboundary] using (faceBoundaryIndex_eq_iff face i i k l).mp h

omit [T2Space M] in
theorem coordinateEdgeEnds_pair (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = coordinates i ∘
      affineChartSegment (basis i (k.succAbove 0)) (basis i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (i : I) (k : Fin 3) :
    ({(coordinateEdgeEnds face coordinates basis (faceBoundaryIndex face i k)).1,
      (coordinateEdgeEnds face coordinates basis (faceBoundaryIndex face i k)).2} :
      Set (CoordinateVertex coordinates basis)) =
    {coordinateCorner coordinates basis i (k.succAbove 0),
      coordinateCorner coordinates basis i (k.succAbove 1)} := by
  let e := faceBoundaryIndex face i k
  have hpair := equal_coordinate_edge_endpoint_sets (coordinates i) (basis i)
    (hsource i) k (faceBoundaryEdge face e) (hinj e.out.1 e.out.2)
    (by dsimp only [e]; rw [faceBoundaryEdge_image, hboundary])
  apply (Set.image_injective.mpr
    (Subtype.val_injective : Function.Injective (Subtype.val : CoordinateVertex coordinates basis → M)))
  simp only [Set.image_insert_eq, Set.image_singleton]
  simpa [coordinateEdgeEnds, coordinateCorner, faceBoundaryEdge, hboundary,
    affineChartSegment, e] using hpair

theorem exists_canonical_adjacentFaces [Finite I] (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hcarrier : ∀ i, (face i).carrier = coordinates i '' convexHull ℝ (range (basis i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = coordinates i ∘
      affineChartSegment (basis i (k.succAbove 0)) (basis i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {coordinates i (basis i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (hcover : (⋃ i, (face i).carrier) = univ) :
    ∃ adjacent : FaceBoundaryEdge face → I × I,
      (∀ e, (adjacent e).1 ≠ (adjacent e).2) ∧
      ∀ e i, (∃ k, faceBoundaryIndex face i k = e) ↔
        i = (adjacent e).1 ∨ i = (adjacent e).2 := by
  classical
  have hmeet (e d : FaceBoundaryEdge face) (hed : e ≠ d) :
      (faceBoundaryEdge face e).map '' Icc (0 : ℝ) 1 ∩
        (faceBoundaryEdge face d).map '' Icc (0 : ℝ) 1 ⊆
      {(faceBoundaryEdge face e).map 0, (faceBoundaryEdge face e).map 1} := by
    apply coordinate_cover_edge_meet face coordinates basis hsource hboundary hinj hinter
      e.out.1 d.out.1 e.out.2 d.out.2
    intro heq
    apply hed
    have h := (faceBoundaryIndex_eq_iff face e.out.1 d.out.1 e.out.2 d.out.2).mpr heq
    exact (Quotient.out_eq e).symm.trans (h.trans (Quotient.out_eq d))
  choose left right hdistinct hexact using fun e =>
    exists_exactly_two_faces_of_coordinate_triangle_cover
      (normalizeFaceBoundary face) (faceBoundaryEdge face) (faceBoundaryIndex face)
      (normalizeFaceBoundary_boundary face)
      (fun e => ⟨e.out.1, e.out.2, Quotient.out_eq e⟩)
      (fun e => hinj e.out.1 e.out.2) hmeet
      coordinates basis hsource hcarrier hfront hcover e
  exact ⟨fun e => (left e, right e), hdistinct, hexact⟩

end PoincareConjecture.Topology.Surface.Euler
