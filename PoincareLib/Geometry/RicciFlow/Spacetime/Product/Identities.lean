import PoincareLib.Geometry.CurveShortening.Evolution.CovariantTheory
import PoincareLib.Geometry.RicciFlow.Spacetime.Product.Metric
import PoincareLib.Geometry.RicciFlow.Spacetime.Product.TimeSpatialPairing
import PoincareLib.Geometry.RicciFlow.Spacetime.Product.Gauss
import PoincareLib.Geometry.RicciFlow.Spacetime.Product.Codazzi

/-!
# The complete actual spacetime identities

Package the actual metric, connection and curvature formulas in the frozen
spacetime output. This follows MT2015Correction (0.1)-(0.2), p. 2, and
Lemma 0.2, pp. 4-6.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- All frozen identities hold for the actual spacetime data;
MT2015Correction (0.1)-(0.2), p. 2, and Lemma 0.2, pp. 4-6. -/
theorem SpacetimeData.identities {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) : SpacetimeIdentities G where
  time_smooth := G.charts.timeVector_smooth
  time_unit := G.time_unit
  time_parallel_time := G.time_parallel_time
  spatial_connection := G.spatial_connection
  spatial_time_vertical := fun q V => G.time_covariant_vertical q (G.charts.horizontal q V)
  spatial_time_pairing := G.spatial_time_pairing
  time_spatial_vertical := G.time_spatial_vertical
  time_spatial_pairing := G.time_spatial_pairing
  gauss := G.gauss
  codazzi := G.codazzi

/-- The genuine open spacetime exists with all its connection and curvature
identities; MT2015Correction p. 2 and Lemma 0.2, pp. 4-6. -/
theorem exists_spacetimeData [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) :
    ∃ G : SpacetimeData F, SpacetimeIdentities G := by
  obtain ⟨C⟩ := nonempty_spacetimeCharts (n := n) (M := M) a b
  obtain ⟨G⟩ := nonempty_spacetimeData_of_charts F C
  exact ⟨G, G.identities⟩

end PoincareMT.M62
