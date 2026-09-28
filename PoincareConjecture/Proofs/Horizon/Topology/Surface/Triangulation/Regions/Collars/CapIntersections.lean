import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.CompatibleCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Caps

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))

theorem vertex_caps_coordinate_intersection
    {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
    {x : D.vertices → Bool × Bool → M}
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    {a b : D.vertices × (Bool × Bool)} (hab : a ≠ b) :
    CoordinateTriangleBoundaryIntersection ((B a.1).coordinates a.2) ((B b.1).coordinates b.2)
      (rightTriangleBasis (B a.1).scale_pos) (rightTriangleBasis (B b.1).scale_pos) := by
  classical
  rcases a with ⟨p, s⟩
  rcases b with ⟨q, t⟩
  by_cases hpq : p = q
  · subst q
    have hst : s ≠ t := fun h => hab (Prod.ext rfl h)
    rcases (B p).intersection_edge_or_vertex hst with ⟨k, hk, hsame⟩ | hpoint
    · apply CoordinateTriangleBoundaryIntersection.subsegment k k 0 1 0 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · simpa only [uIcc_of_le zero_le_one, (B p).carrier_eq, (B p).boundary_map] using hk
      · simpa only [uIcc_of_le zero_le_one, (B p).carrier_eq, (B p).boundary_map] using
          hk.trans hsame
    · apply CoordinateTriangleBoundaryIntersection.point (p : M)
      · rw [← (B p).face_frontier_eq_coordinates s]
        exact (B p).center_mem_frontier s
      · rw [← (B p).face_frontier_eq_coordinates t]
        exact (B p).center_mem_frontier t
      · rw [← (B p).carrier_eq s, ← (B p).carrier_eq t, hpoint]
  · apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (B p).carrier_eq s, ← (B q).carrier_eq t]
    exact (hdisjoint p q hpq).mono ((B p).carrier_subset_patch s) ((B q).carrier_subset_patch t)

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
