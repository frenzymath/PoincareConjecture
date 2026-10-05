import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.RadialFrontierConeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonFinitePLTriangleBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonSliceCoordinates

/-!
# The exact disk bounded by a radial polygon

A simple polygon on a convex frontier cones to an actual
finite PL disk with the original polygon as its entire rim.
The planar model is the existing triangle boundary chart.
See Alexander 1924, pp. 6--7, Cairns 1940, p. 802 and
M76 derivation 248.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- The cone on a simple whole polygon in a convex frontier
is an actual finite PL disk, with exactly that polygon as its
specified boundary. No planarity of the source polygon is
required. See Alexander pp. 6--7 and M76 derivation 248. -/
theorem isFinitePLBallPair_radial_cone (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {C : Set E} (hcv : Convex ℝ C) (hC0 : (0 : E) ∈ interior C)
    (hPC : P.boundary ℝ ⊆ frontier C) :
    IsFinitePLBallPair (ℝ × ℝ) (convexJoin ℝ {0} (P.boundary ℝ)) (P.boundary ℝ) := by
  let T := referenceTriangle 0
  have hT : AffineIndependent ℝ T := affineIndependent_referenceTriangle 0
  let b : AffineBasis (Fin 3) ℝ (ℝ × ℝ) := ⟨T, hT,
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Module.finrank_prod])⟩
  obtain ⟨e, he, _⟩ := P.exists_finitePL_triangle_boundary_model hP hinj T hT
  exact he.isFinitePLBallPair_radial_cone hcv hC0 hPC
    ⟨P 0, P.vertex_mem_boundary 0⟩ ((finite_range T).isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) ⟨_, b.centroid_mem_interior_convexHull⟩

end Polygon
