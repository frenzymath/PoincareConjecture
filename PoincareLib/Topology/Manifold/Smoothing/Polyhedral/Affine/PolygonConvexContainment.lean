import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonTriangulation

/-!
# Convex containment of closed polygon fillings

A frugal triangulation uses only the original polygon vertices.
Consequently every convex set containing those vertices contains
the whole closed inside. See Erickson, Simple Polygons, pp. 8--9
and M76 derivation 139.
-/

set_option autoImplicit false

open Set Geometry

namespace Polygon

/-- A convex set containing every vertex of a simple planar
polygon contains its entire closed inside. The convex set may
be open. See Erickson pp. 8--9 and M76 derivation 139. -/
theorem closure_inside_subset_convex {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {C : Set (ℝ × ℝ)} (hC : Convex ℝ C) (hPC : range P ⊆ C) :
    closure P.inside ⊆ C := by
  obtain ⟨K, hK⟩ := P.exists_triangulation hP hinj
  rw [← hK.space_eq]
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  apply convexHull_min (fun y hy => hPC (hK.vertices_subset ?_)) hC hxt
  rw [SimplicialComplex.vertices_eq]
  exact subset_biUnion_of_mem ht hy

end Polygon
