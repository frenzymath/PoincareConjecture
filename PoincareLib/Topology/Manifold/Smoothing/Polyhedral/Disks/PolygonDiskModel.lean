import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.UnitBallPairs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonTriangleRegion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonReindex

/-!
# Triangle disk models and cyclic relabeling

Independent triangles supply the base of the disk-pair induction.
Cyclic relabeling retains the carrier and boundary simultaneously.
See Erickson pp. 8--10 and M76 derivation 118.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- An independent planar triangle with its exact frontier
is a ball pair. See M76 derivation 118. -/
theorem isUnitBallPair_convexHull_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : AffineIndependent ℝ P) :
    IsUnitBallPair (ℝ × ℝ) (convexHull ℝ (range P)) (frontier (convexHull ℝ (range P))) := by
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨P, hP,
    hP.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  exact isUnitBallPair_of_compact_convex ((finite_range P).isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) ⟨_, b.centroid_mem_interior_convexHull⟩

/-- The canonical closed region of a simple triangle, with
its polygon boundary, is a disk pair. See derivation 118. -/
theorem isUnitBallPair_triangle (P : Polygon (ℝ × ℝ) 3)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    IsUnitBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  rw [← P.frontier_closure_inside hP hinj, P.closure_inside_triangle hP hinj]
  exact P.isUnitBallPair_convexHull_triangle (P.affineIndependent_triangle hP hinj)

/-- A disk model of a cyclic relabeling is a disk model of
the original polygon, including its boundary. See derivation 118. -/
theorem isUnitBallPair_of_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i))
    (h : IsUnitBallPair (ℝ × ℝ) (closure (P.reindex e).inside) ((P.reindex e).boundary ℝ)) :
    IsUnitBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  simpa only [P.inside_reindex e he, P.boundary_reindex e he] using h

end Polygon
