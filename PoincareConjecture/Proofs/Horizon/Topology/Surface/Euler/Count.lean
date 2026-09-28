import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Incidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Connectivity
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Boundary

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.Euler

theorem eulerCount_le_two_of_coordinate_cover
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [ConnectedSpace M] {I : Type*} [Finite I]
    (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hcarrier : ∀ i, (face i).carrier = coordinates i '' convexHull ℝ (range (basis i)))
    (hboundary : ∀ i k, ((face i).boundary k).map =
      coordinates i ∘ affineChartSegment
        (basis i (k.succAbove 0)) (basis i (k.succAbove 1)))
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
    (Nat.card (CoordinateVertex coordinates basis) : ℤ) -
      Nat.card (FaceBoundaryEdge face) + Nat.card I ≤ 2 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype (FaceBoundaryEdge face) := Fintype.ofFinite _
  let : Fintype (CoordinateVertex coordinates basis) := Fintype.ofFinite _
  have : Nonempty I := by
    obtain ⟨p⟩ := (inferInstance : Nonempty M)
    obtain ⟨i, _⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
    exact ⟨i⟩
  have : Nonempty (CoordinateVertex coordinates basis) :=
    ⟨coordinateCorner coordinates basis (Classical.arbitrary I) 0⟩
  obtain ⟨adjacent, hdistinct, hexact⟩ := exists_canonical_adjacentFaces
    face coordinates basis hsource hcarrier hboundary hinj hinter hfront hcover
  have hdual := endpointConnected_faces face coordinates basis hsource hcarrier
    hcover hinter adjacent hexact
  have hends := coordinateEdgeEnds_pair face coordinates basis hsource hboundary hinj
  have hprimal := endpointConnected_of_dual
    (faceBoundaryIndex face) (coordinateCorner coordinates basis)
    (coordinateEdgeEnds face coordinates basis) adjacent hexact hends
    (fun v => by
      obtain ⟨⟨i, k⟩, h⟩ := coordinateCorner_surjective coordinates basis v
      exact ⟨i, k, h⟩) hdual
  have hcomp := boundary_comp_eq_zero
    (faceBoundaryIndex face) (coordinateCorner coordinates basis)
    (coordinateEdgeEnds face coordinates basis) adjacent
    (coordinate_faceBoundaryIndex_injective face coordinates basis hsource hboundary)
    hdistinct hexact hends
  simpa only [Nat.card_eq_fintype_card] using
    PoincareConjecture.Surface.Combinatorial.Incidence.eulerCount_le_two
      (coordinateEdgeEnds face coordinates basis) adjacent hprimal hdual hcomp

end PoincareConjecture.Topology.Surface.Euler
