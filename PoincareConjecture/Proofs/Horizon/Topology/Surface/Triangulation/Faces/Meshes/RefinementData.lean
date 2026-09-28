import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.BoundarySubdivision

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

structure CompatibleCoordinateTriangleRefinement {I : Type v}
    (F : I → OpenPartialHomeomorph Plane M) (b : I → AffineBasis (Fin 3) ℝ Plane) where
  marks : I → Finset M
  subdivision : ∀ i, SmoothTriangleBoundarySubdivisionWithRefinement (F i) (b i) (marks i)
  intersections : ∀ (a d : (i : I) × (subdivision i).mesh.Triangle), a ≠ d →
    (∃ k l : Fin 3,
      ((subdivision a.1).face a.2).carrier ∩ ((subdivision d.1).face d.2).carrier =
        (((subdivision a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 ∧
      (((subdivision a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 =
        (((subdivision d.1).face d.2).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ w : Fin 3,
      ((subdivision a.1).face a.2).carrier ∩ ((subdivision d.1).face d.2).carrier ⊆
        {F a.1 (meshTriangleBasis (subdivision a.1).mesh a.2 w)}
  intersection_frontier : ∀ (a d : (i : I) × (subdivision i).mesh.Triangle), a ≠ d →
    ((subdivision a.1).face a.2).carrier ∩ ((subdivision d.1).face d.2).carrier ⊆
      frontier ((subdivision a.1).face a.2).carrier
  cover : (⋃ a : (i : I) × (subdivision i).mesh.Triangle,
    ((subdivision a.1).face a.2).carrier) = univ

namespace CompatibleCoordinateTriangleRefinement

variable {I : Type v} {F : I → OpenPartialHomeomorph Plane M}
  {b : I → AffineBasis (Fin 3) ℝ Plane} (R : CompatibleCoordinateTriangleRefinement F b)

abbrev Child := (i : I) × (R.subdivision i).mesh.Triangle

abbrev mesh (i : I) : TriangleMesh := (R.subdivision i).mesh

abbrev face (a : R.Child) : SmoothFace M := (R.subdivision a.1).face a.2

abbrev coordinates (a : R.Child) : OpenPartialHomeomorph Plane M := F a.1

noncomputable abbrev basis (a : R.Child) : AffineBasis (Fin 3) ℝ Plane :=
  meshTriangleBasis (R.mesh a.1) a.2

omit [T2Space M] in
theorem source_subset (a : R.Child) :
    convexHull ℝ (range (R.basis a)) ⊆ (R.coordinates a).source :=
  (R.subdivision a.1).source_subset a.2

omit [T2Space M] in
theorem mesh_source (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source) (i : I) :
    (R.mesh i).toPlaneComplex.support ⊆ (F i).source := by
  rw [(R.subdivision i).support]
  exact hsource i

omit [T2Space M] in
theorem carrier_eq (a : R.Child) :
    (R.face a).carrier = R.coordinates a '' convexHull ℝ (range (R.basis a)) :=
  (R.subdivision a.1).carrier_eq a.2

omit [T2Space M] in
theorem boundary_map (a : R.Child) (k : Fin 3) :
    ((R.face a).boundary k).map = R.coordinates a ∘
      affineChartSegment (R.basis a (k.succAbove 0)) (R.basis a (k.succAbove 1)) :=
  (R.subdivision a.1).boundary_map a.2 k

omit [T2Space M] in
theorem boundary_injective (a : R.Child) (k : Fin 3) :
    InjOn ((R.face a).boundary k).map (Icc (0 : ℝ) 1) :=
  (R.subdivision a.1).boundary_injective a.2 k

end CompatibleCoordinateTriangleRefinement

end PoincareConjecture.Topology.Surface
