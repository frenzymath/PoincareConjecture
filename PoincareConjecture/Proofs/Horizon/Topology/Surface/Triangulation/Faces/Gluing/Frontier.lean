import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing.Subsegments

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

namespace Poincare.Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {I : Type v} [Finite I]

theorem frontier_iUnion_subset_iUnion_frontier_of_isClosed
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i)) :
    frontier (⋃ i, A i) ⊆ ⋃ i, frontier (A i) := by
  intro p hp
  obtain ⟨i, hpi⟩ := mem_iUnion.mp ((isClosed_iUnion_of_finite hclosed).frontier_subset hp)
  refine mem_iUnion.mpr ⟨i, subset_closure hpi, ?_⟩
  intro hpint
  exact hp.2 (interior_mono (subset_iUnion A i) hpint)

theorem closure_interior_iUnion_of_regular_closed
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i) :
    closure (interior (⋃ i, A i)) = ⋃ i, A i := by
  apply subset_antisymm (closure_minimal interior_subset (isClosed_iUnion_of_finite hclosed))
  apply iUnion_subset
  intro i
  rw [← hregular i]
  exact closure_mono (interior_mono (subset_iUnion A i))

end Poincare.Topology

namespace PoincareConjecture.Topology.Surface

universe u v w

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem closure_interior_iUnion_coordinate_triangle_carriers
    {I : Type v} [Finite I] (face : I → SmoothFace M)
    (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
    (hcarrier : ∀ i, (face i).carrier = coordinates i '' convexHull ℝ (range (basis i))) :
    closure (interior (⋃ i, (face i).carrier)) = ⋃ i, (face i).carrier := by
  apply Poincare.Topology.closure_interior_iUnion_of_regular_closed
    (fun i => (face i).carrier) (fun i => (face i).isClosed_carrier)
  intro i
  rw [hcarrier]
  exact coordinate_triangle_closure_interior (coordinates i) (basis i) (hsource i)

section SharedSubsegments

variable {I : Type v} [Finite I] {J : Type w}
  (face : I → SmoothFace M)
  (coordinates : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
  (basis : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
  (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (coordinates i).source)
  (hcarrier : ∀ i, (face i).carrier = coordinates i '' convexHull ℝ (range (basis i)))
  (hboundary : ∀ i k, ((face i).boundary k).map = coordinates i ∘
    affineChartSegment (basis i (k.succAbove 0)) (basis i (k.succAbove 1)))
  (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
  (left right : J → I) (leftEdge rightEdge : J → Fin 3)
  (a b c d : J → ℝ)
  (hbounds : ∀ j, a j ∈ Icc (0 : ℝ) 1 ∧ b j ∈ Icc (0 : ℝ) 1 ∧
    c j ∈ Icc (0 : ℝ) 1 ∧ d j ∈ Icc (0 : ℝ) 1)
  (hinter : ∀ j, (face (left j)).carrier ∩ (face (right j)).carrier ⊆
    frontier (face (left j)).carrier)
  (hshared : ∀ j, ((face (left j)).boundary (leftEdge j)).map '' Icc (a j) (b j) =
    ((face (right j)).boundary (rightEdge j)).map '' Icc (c j) (d j))

include hsource hcarrier hboundary hinj hbounds hinter hshared in

theorem iUnion_coordinate_triangles_shared_subsegments
    : closure (interior (⋃ i, (face i).carrier)) = (⋃ i, (face i).carrier) ∧
      (⋃ j, (((face (left j)).boundary (leftEdge j)).map '' Ioo (a j) (b j)) ∩
        (((face (right j)).boundary (rightEdge j)).map '' Ioo (c j) (d j))) ⊆
        interior (⋃ i, (face i).carrier) ∧
      frontier (⋃ i, (face i).carrier) ⊆ (⋃ i, frontier (face i).carrier) \
        (⋃ j, (((face (left j)).boundary (leftEdge j)).map '' Ioo (a j) (b j)) ∩
          (((face (right j)).boundary (rightEdge j)).map '' Ioo (c j) (d j))) := by
  have hglued :
      (⋃ j, (((face (left j)).boundary (leftEdge j)).map '' Ioo (a j) (b j)) ∩
        (((face (right j)).boundary (rightEdge j)).map '' Ioo (c j) (d j))) ⊆
        interior (⋃ i, (face i).carrier) := by
    intro p hp
    obtain ⟨j, ⟨t, ht, htp⟩, ⟨s, hs, hsp⟩⟩ := mem_iUnion.mp hp
    have hpoint := mem_interior_union_of_coordinate_triangles_shared_subsegment
      (face (left j)) (face (right j)) (coordinates (left j)) (coordinates (right j))
      (basis (left j)) (basis (right j)) (hsource (left j)) (hsource (right j))
      (hcarrier (left j)) (hcarrier (right j)) (hboundary (left j)) (hboundary (right j))
      (hinter j) (leftEdge j) (rightEdge j) (hinj (left j) (leftEdge j))
      (hinj (right j) (rightEdge j)) (hbounds j).1 (hbounds j).2.1
      (hbounds j).2.2.1 (hbounds j).2.2.2 ht hs (htp.trans hsp.symm) (hshared j)
    exact htp ▸ interior_mono
      (union_subset (subset_iUnion (fun i => (face i).carrier) (left j))
        (subset_iUnion (fun i => (face i).carrier) (right j))) hpoint
  refine ⟨closure_interior_iUnion_coordinate_triangle_carriers face coordinates basis hsource hcarrier,
    hglued, ?_⟩
  intro p hp
  exact ⟨Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
    (fun i => (face i).carrier) (fun i => (face i).isClosed_carrier) hp,
    fun hps => hp.2 (hglued hps)⟩

include hsource hcarrier hboundary hinj hbounds hinter hshared in

theorem frontier_iUnion_coordinate_triangles_subset_of_shared_subsegments
    (remaining : Set M)
    (hremaining : ∀ i, frontier (face i).carrier ⊆ remaining ∪
      (⋃ j, (((face (left j)).boundary (leftEdge j)).map '' Ioo (a j) (b j)) ∩
        (((face (right j)).boundary (rightEdge j)).map '' Ioo (c j) (d j)))) :
    frontier (⋃ i, (face i).carrier) ⊆ remaining := by
  have h := iUnion_coordinate_triangles_shared_subsegments face coordinates basis
    hsource hcarrier hboundary hinj left right leftEdge rightEdge a b c d hbounds hinter hshared
  intro p hp
  obtain ⟨hfront, hnot⟩ := h.2.2 hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hfront
  exact (hremaining i hi).resolve_right hnot

end SharedSubsegments

end PoincareConjecture.Topology.Surface
