import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangulation

set_option autoImplicit false

open Set Geometry

namespace Polygon

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
