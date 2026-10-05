import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonBoundedRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ComplementaryRegionClosures

/-!
# The compact closed region enclosed by a polygon

The closure of the bounded complementary region is compact,
with the original region as interior, the polygon as frontier,
and connected exterior. See Erickson, Simple Polygons,
pp. 4, 6--8 and M76 derivation 100.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- A simple planar polygon encloses an open connected region
with compact closure, exact interior and frontier, and connected
exterior. A disk parameterization is a further construction.
See Erickson pp. 4, 6--8 and M76 derivation 100. -/
theorem exists_compact_region {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      interior (closure U) = U ∧ frontier (closure U) = P.boundary ℝ ∧
      IsConnected (closure U)ᶜ := by
  obtain ⟨U, V, hU, _, hUc, hVc, hdis, hcover, hfrontU, hfrontV, hbound, _⟩ :=
    P.exists_bounded_complementary_regions hP hinj
  refine ⟨U, hU, hUc, hbound.isCompact_closure,
    interior_closure_eq_of_complementary_regions hcover hdis hfrontU hfrontV,
    frontier_closure_eq_of_complementary_regions hcover hdis hfrontU hfrontV, ?_⟩
  rwa [closure_eq_compl_of_complementary_regions hcover hdis hfrontU, compl_compl]

end Polygon
