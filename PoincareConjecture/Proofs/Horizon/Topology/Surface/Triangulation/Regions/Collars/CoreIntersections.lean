


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.CompatibleCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Intersections








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem core_segment_image (p q : Plane) :
    affineChartSegment p q '' Icc (0 : ℝ) 1 = affineSegment ℝ p q := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem core_vertex_frontier (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    b i ∈ frontier (convexHull ℝ (range b)) := by
  rw [frontier_convexHull_affineBasis_fin3_segments]
  fin_cases i
  · exact mem_iUnion.mpr ⟨1, by
      change b 0 ∈ affineSegment ℝ (b 0) (b 2)
      rw [affineSegment_eq_segment]
      exact left_mem_segment ℝ _ _⟩
  · exact mem_iUnion.mpr ⟨0, by
      change b 1 ∈ affineSegment ℝ (b 1) (b 2)
      rw [affineSegment_eq_segment]
      exact left_mem_segment ℝ _ _⟩
  · exact mem_iUnion.mpr ⟨0, by
      change b 2 ∈ affineSegment ℝ (b 1) (b 2)
      rw [affineSegment_eq_segment]
      exact right_mem_segment ℝ _ _⟩

private theorem mesh_triangle_inter_subset_frontier (T : TriangleMesh)
    (s t : T.Triangle) (hst : s ≠ t) :
    convexHull ℝ (range (meshTriangleBasis T s)) ∩
      convexHull ℝ (range (meshTriangleBasis T t)) ⊆
        frontier (convexHull ℝ (range (meshTriangleBasis T s))) := by
  rcases meshTriangleBasis_pair_intersections T s t hst with ⟨k, l, hk, _⟩ | ⟨v, hv, hsub⟩
  · rw [hk, frontier_convexHull_affineBasis_fin3_segments]
    exact subset_iUnion (fun i : Fin 3 => affineSegment ℝ
      (meshTriangleBasis T s (i.succAbove 0)) (meshTriangleBasis T s (i.succAbove 1))) k
  · intro z hz
    rw [mem_singleton_iff.mp (hsub hz)]
    obtain ⟨i, hi⟩ : v ∈ range (T.orderedVertex s) := by
      rw [T.range_orderedVertex]
      exact hv
    rw [← hi]
    exact core_vertex_frontier (meshTriangleBasis T s) i

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M] in


theorem mesh_coordinate_triangle_intersection (T : TriangleMesh)
    (C : OpenPartialHomeomorph Plane M) (hsource : T.toPlaneComplex.support ⊆ C.source)
    (s t : T.Triangle) (hst : s ≠ t) :
    CoordinateTriangleBoundaryIntersection C C (meshTriangleBasis T s) (meshTriangleBasis T t) := by
  have hs := (meshTriangleBasis_subset_support T s).trans hsource
  have ht := (meshTriangleBasis_subset_support T t).trans hsource
  have hinter : (C '' convexHull ℝ (range (meshTriangleBasis T s))) ∩
      (C '' convexHull ℝ (range (meshTriangleBasis T t))) =
        C '' (convexHull ℝ (range (meshTriangleBasis T s)) ∩
          convexHull ℝ (range (meshTriangleBasis T t))) := (C.injOn.image_inter hs ht).symm
  rcases meshTriangleBasis_pair_intersections T s t hst with ⟨k, l, hk, hl⟩ | ⟨v, _, hv⟩
  · apply CoordinateTriangleBoundaryIntersection.subsegment k l 0 1 0 1
      (by simp) (by simp) (by simp) (by simp)
    · rw [hinter, hk, uIcc_of_le zero_le_one, ← core_segment_image, image_image]
      rfl
    · rw [hinter, hk, hl, uIcc_of_le zero_le_one, ← core_segment_image, image_image]
      rfl
  · by_cases hn : ((C '' convexHull ℝ (range (meshTriangleBasis T s))) ∩
        (C '' convexHull ℝ (range (meshTriangleBasis T t)))).Nonempty
    · obtain ⟨q, hq⟩ := hn
      obtain ⟨z, hz, rfl⟩ := hinter ▸ hq
      apply CoordinateTriangleBoundaryIntersection.point (C z)
      · exact mem_image_of_mem C (mesh_triangle_inter_subset_frontier T s t hst hz)
      · exact mem_image_of_mem C (mesh_triangle_inter_subset_frontier T t s hst.symm ⟨hz.2, hz.1⟩)
      · rw [hinter]
        rintro _ ⟨w, hw, rfl⟩
        exact congrArg C ((mem_singleton_iff.mp (hv hw)).trans (mem_singleton_iff.mp (hv hz)).symm)
    · exact .disjoint (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn))

namespace FiniteChartRegionDecomposition

variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in

theorem region_disjoint_closure {R S : D.regions} (hne : R ≠ S) :
    Disjoint (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
      (closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S)) := by
  apply disjoint_left.mpr
  intro q hqR hqS
  exact disjoint_left.mp (D.regions_disjoint hne) hqR
    (D.region_closure_diff_arrangement_subset S
      ⟨hqS, connectedComponentIn_subset _ _ hqR⟩)

omit [T2Space M] in


theorem core_parent_coordinate_intersection
    {R S : D.regions} (hne : R ≠ S)
    (T : TriangleMesh) (C F : OpenPartialHomeomorph Plane M)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hcore : C '' T.toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hparent : F '' convexHull ℝ (range b) ⊆
      closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S))
    (t : T.Triangle) :
    CoordinateTriangleBoundaryIntersection C F (meshTriangleBasis T t) b :=
  .disjoint ((D.region_disjoint_closure hne).mono
    ((image_mono (meshTriangleBasis_subset_support T t)).trans hcore) hparent)

omit [T2Space M] in
theorem cross_region_core_coordinate_intersection
    {R S : D.regions} (hne : R ≠ S)
    (T U : TriangleMesh) (C F : OpenPartialHomeomorph Plane M)
    (hT : C '' T.toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hU : F '' U.toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S)
    (t : T.Triangle) (u : U.Triangle) :
    CoordinateTriangleBoundaryIntersection C F (meshTriangleBasis T t) (meshTriangleBasis U u) :=
  D.core_parent_coordinate_intersection hne T C F (meshTriangleBasis U u) hT
    (((image_mono (meshTriangleBasis_subset_support U u)).trans hU).trans subset_closure) t

omit [T2Space M] in
theorem cross_region_core_cap_coordinate_intersection
    {R S : D.regions} (hne : R ≠ S)
    (T : TriangleMesh) (C : OpenPartialHomeomorph Plane M)
    {radius : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch radius p}
    {x : Bool × Bool → M} (caps : ChartCircleArrangementVertexPatch.VertexCapFaces P x)
    (s : Bool × Bool)
    (hcore : C '' T.toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hcap : (caps.face s).carrier ⊆
      closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S))
    (t : T.Triangle) :
    CoordinateTriangleBoundaryIntersection C (caps.coordinates s)
      (meshTriangleBasis T t) (rightTriangleBasis caps.scale_pos) := by
  apply D.core_parent_coordinate_intersection hne T C (caps.coordinates s) _ hcore _ t
  rwa [← caps.carrier_eq]

omit [T2Space M] in
theorem cross_region_core_band_coordinate_intersection
    {R S : D.regions} (hne : R ≠ S)
    (T : TriangleMesh) (C F : OpenPartialHomeomorph Plane M)
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (hcore : C '' T.toPlaneComplex.support ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)
    (hband : B.carrier ⊆
      closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ S))
    (t : T.Triangle) (j : Fin B.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection C (B.faceCoordinates j)
      (meshTriangleBasis T t) (B.faceBasis j) := by
  apply D.core_parent_coordinate_intersection hne T C (B.faceCoordinates j) _ hcore _ t
  rw [← B.face_carrier_eq_coordinates]
  exact (subset_iUnion (fun v => (B.face v).carrier) j).trans hband

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
