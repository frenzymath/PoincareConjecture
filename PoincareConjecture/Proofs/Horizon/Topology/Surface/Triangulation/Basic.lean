


import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Compactness.Compact
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Basic








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]


structure SmoothEdge (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] where
  map : ℝ → M
  smooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ map (Icc (0 : ℝ) 1)
  regular : ∀ t ∈ Ioo (0 : ℝ) 1,
    Function.Injective (mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) map t)


structure SmoothFace (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] where
  map : EuclideanSpace ℝ (Fin 2) → M
  source : Set (EuclideanSpace ℝ (Fin 2))
  source_compact : IsCompact source
  source_triangle : ∃ a b c : EuclideanSpace ℝ (Fin 2),
    source = convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))
  smooth : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓡 2) ∞ map source
  carrier : Set M
  carrier_eq_image : carrier = map '' source
  chart : M
  carrier_subset_chart : carrier ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) chart).source
  boundary : Fin 3 → SmoothEdge M
  boundary_carrier : frontier carrier = ⋃ i, (boundary i).map '' Icc (0 : ℝ) 1


structure FiniteSmoothTriangulation where
  (faces edges vertices : Type)
  [faces_finite : Fintype faces]
  [edges_finite : Fintype edges]
  [vertices_finite : Fintype vertices]
  face : faces → SmoothFace M
  edge : edges → SmoothEdge M
  vertex : vertices → M
  face_edge : faces → Fin 3 → edges
  edge_face : edges → Fin 2 → faces
  face_edge_map : ∀ f i, (face f).boundary i = edge (face_edge f i)
  edge_face_boundary : ∀ e j, ∃ i, face_edge (edge_face e j) i = e
  edge_faces_distinct : ∀ e, edge_face e 0 ≠ edge_face e 1
  edge_face_exact : ∀ e f i, face_edge f i = e →
    f = edge_face e 0 ∨ f = edge_face e 1
  face_cover : (⋃ f, (face f).carrier) = (univ : Set M)
  face_intersection : ∀ f g, f ≠ g →
    (∃ e, (face f).carrier ∩ (face g).carrier = (edge e).map '' Icc (0 : ℝ) 1) ∨
    (∃ v, (face f).carrier ∩ (face g).carrier ⊆ {vertex v})









structure FiniteSmoothTriangulationWithCoordinates where
  triangulation : FiniteSmoothTriangulation (M := M)
  coordinates : triangulation.faces → OpenPartialHomeomorph
    (EuclideanSpace ℝ (Fin 2)) M
  basis : triangulation.faces → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))
  coordinates_smooth : ∀ f,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates f) (coordinates f).source
  coordinates_symm_smooth : ∀ f,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates f).symm (coordinates f).target
  basis_subset_source : ∀ f,
    convexHull ℝ (range (basis f)) ⊆ (coordinates f).source
  carrier_eq_coordinates : ∀ f,
    (triangulation.face f).carrier =
      coordinates f '' convexHull ℝ (range (basis f))
  boundary_side_image : ∀ f k,
    ((triangulation.face f).boundary k).map '' Icc (0 : ℝ) 1 =
      coordinates f '' affineSegment ℝ (basis f (k.succAbove 0))
        (basis f (k.succAbove 1))


theorem FiniteSmoothTriangulation.incident_iff
    (T : FiniteSmoothTriangulation (M := M)) (e : T.edges) (f : T.faces) :
    (∃ i, T.face_edge f i = e) ↔ f = T.edge_face e 0 ∨ f = T.edge_face e 1 := by
  constructor
  · rintro ⟨i, hi⟩
    exact T.edge_face_exact e f i hi
  · rintro (rfl | rfl)
    · exact T.edge_face_boundary e 0
    · exact T.edge_face_boundary e 1

end PoincareConjecture.Topology.Surface
